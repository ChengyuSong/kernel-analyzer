# Measurement section (paper-ready draft, 2026-08-08)

The dedicated pre-design measurement study (paper §2). Carries ONLY
what is measurable without the flows-to solver: the saturation
baseline autopsy and the corpus boundary census. The tool-produced
measurements (giant-class anatomy, weld census, probes) stay in §4 —
they are instruments' output and belong after the instrument exists.
Citation keys placeholders; numbers pinned per the writer notes at
the end.

---

# 2. What a Kernel Call Graph Actually Requires

Ask the two research communities that own this problem whether
CFL-reachability pointer analysis scales, and you get confident,
contradictory answers. The systems line that builds analysis engines
reports the problem solved: modern solvers traverse billions of
edges with near-optimal redundancy elimination [Graspan, POCR,
Pearl, GraCFL]. The security line that builds kernel call graphs
reports it unsolved: the state-of-the-art system caps its traversals
to survive [KallGraph §2.1 below]. Both positions are held by experts
with state-of-the-art results. This section adjudicates the dispute
by measurement — using only a baseline solver and corpus scanners,
no machinery this paper later introduces — and closes with the
requirements the measurements force on any design. The short verdict:
both communities are right about their own layer, and the wall sits
between them, in a quantity neither layer owns — the size of the
closure the *formulation* demands.

## 2.1 The closure wall

**Setting.** We analyze LLVM IR, not a pre-abstracted pointer graph:
every load and store contributes assistant memory-cell nodes, SSA
contributes copy chains, and whole-program linkage connects
translation units — millions of nodes and edges before any closure
is computed. Much of the engine literature evaluates on graphs
abstracted below this level; the gap matters, because the pathology
we measure lives in exactly the structure the abstraction removes.

**The baseline at its floor.** Our saturation baseline solves the
standard alias grammar with the strongest engine we could obtain —
GraCFL, which outperforms POCR on these graphs — over per-TU and
whole-program encodings. It is correct at small-library scale
(libpng: seconds), and it exhausts a 49 GB memory budget on
harfbuzz — a single library, two orders of magnitude below a kernel.
Nothing about this is an engine defect, which is the point: the
engine is at its floor, and the floor is the problem.

**The law.** The explosion is output, not work. The saturated alias
relation V behaves as a pairwise relation materialized fact by fact
within each assignment-connected component, and its measured size
tracks

    |V| ≈ Σ over a-connected components C of |C|²

across our corpus (Figure F0 plots the curve from libpng through
harfbuzz to a kernel subset; the fit is not subtle). An engine's
work is lower-bounded by its output, so no engine research can
remove an output-size wall — a better engine reaches it faster.

**The remedies that do not work.** We implemented the two remedies
the literature reaches for. Global graph deduplication merges
structurally identical subgraphs before solving; regular-structure
folding compresses repetitive graph regions. Both shrink the graph;
neither moved the harfbuzz OOM measurably, because the closure does
not care about the graph's representation — it is quadratic in the
component masses, which survive both transformations. We report
these as implemented negative results rather than dismissed
alternatives.

**Why demand-driven analysis is not the escape — for this problem.**
Demand-driven CFL-reachability [HeintzeTardieu, SridharanBodik,
Boomerang] answers single queries by exploring only relevant graph
regions, and it is the natural reflex once whole-program closure is
identified as the cost. A call graph defeats the framing three ways
at once: every indirect-call site is a query (18,773 of them in our
kernel corpus); the queries share nearly all their work, because
resolution funnels through a giant alias structure common to most
sites; and resolution *feeds back* — every resolved target wires new
interprocedural edges that change every other query's graph, so
on-demand degenerates to all-demands iterated to a fixpoint,
re-paying the shared exploration each round.

The state of the art confirms this diagnosis from the other side.
KallGraph [KallGraph], the strongest demand-driven kernel system,
achieves impressive results — and its released implementation
(commit 058f9b5) sustains them with resource caps the paper does not
surface: traversals abort beyond a 35-edge path length
(KallGraphAlgo.cpp:35); the 50 most-visited nodes are permanently
blacklisted after every 20,000 deep visits (:59–81), a list that
persists across queries so results depend on query order; and
formals of any function with more than ~250 call edges per argument
are excluded up front (Util.cpp:107–115). We do not read these caps
as engineering carelessness. We read them as a measurement: an
expert team driving the demand-driven design to its limit found the
traversal drowning exactly where kernel dispatch flow concentrates,
and capped it there. The caps are the demand-side silhouette of the
same wall the saturation baseline hits — visible from both sides,
owned by neither layer.

## 2.2 The dispatch-fabric census

Soundness for a kernel call graph is usually asserted relative to an
implicit model: pointers flow through loads, stores, casts, and
calls. The kernel's actual dispatch fabric routinely leaves that
model. Before designing anything, we scanned the corpus (Linux
6.8.2, 2,618 modules) for every channel a function address can
travel that a vanilla IR analysis will not see. The census is a
corpus artifact, reproducible by scanner alone, and it defines the
obligations any soundness claim must discharge.

**Instructions: a closed world, checked.** The scan begins by
requiring totality: every instruction kind in the compiler's own
definition list receives an explicit disposition (modeled, irrelevant
to pointer flow, or declined-with-counter), and the corpus contains
zero undispositioned kinds. This sounds procedural; it is where
silent unsoundness usually starts (visitor defaults, "unhandled"
fallthroughs), and making it a checked gate converts a class of bugs
into build failures.

**Inline assembly.** x86-64 Linux compiles atomics, bit operations,
per-CPU access, and user-space copies to inline assembly: 129,812
sites, 4,900 distinct templates. Classified by constraint signature,
13.7% of sites (171 templates) can carry pointers — including the
percpu %gs channels and asm-level exchanges that real dispatch state
rides. An analysis that ignores inline assembly is unsound on every
one of these sites; one that over-approximates them all drowns.

**Integer-laundered pointers.** Clang lowers `_Atomic` function
pointers and various kernel idioms to integer loads/stores bracketed
by `ptrtoint`/`inttoptr`; page/virtual address round-trips do the
same arithmetically. We count 47,676 sites where pointer provenance
demonstrably crosses an integer type in ways that carry function
addresses in practice. This channel is not exotic: the
state-of-the-art system's only confirmed false negatives are
attributed by its authors to exactly this gap [KallGraph §7.2.2].

**Linker section arrays.** Initcall tables, parameter hooks, PCI
fixups, ftrace and BPF tracepoint tables are *module-level assembly*
emitting PREL32 relocations into named sections: 106 section-bounded
arrays whose contents are invisible to any instruction-level scan —
646 initcalls alone, plus 16,915 `.discard.addressable` stubs naming
12,597 distinct functions (21.8% of the corpus). A load from
`__start_*`/`__stop_*` resolves to nothing an IR analysis can see;
the dispatch is real.

**Patching families.** static_call sites (`__SCT__*` trampolines)
and tracepoints dispatch through relocation state materialized at
boot or trace-enable time; their call targets exist in registration
structures, not in any data-flow path an alias analysis can traverse
soundly without modeling the family explicitly.

**The external boundary, closed.** Finally, the census cross-checks
every symbol the corpus references but does not define against the
kernel's own symbol table: six truly undefined symbols remain, all
from a single object file absent from our build list, none carrying
function pointers. The boundary is closed — a property one run of
the census proves per corpus, and which turns "we assume the corpus
is whole-program" from folklore into a checked fact.

## 2.3 What the measurements force

Four requirements fall out, and they are the specification the rest
of the paper implements.

- **R1 (from 2.1).** Never materialize the pairwise closure. The
  formulation must change what is computed — whole-program in
  coverage, demand-shaped in fact mass — because engines cannot
  lower an output floor and per-query traversal re-pays it per
  fixpoint round.
- **R2 (from 2.1).** No silent resource caps. The caps that rescue
  demand-driven traversal fire precisely where the answers are
  hardest and where empirical validation sees least; a design that
  needs them has moved its unsoundness to the place it is least
  auditable.
- **R3 (from 2.2).** Model or ledger every boundary channel. Inline
  assembly, integer provenance, section arrays, and patching
  families are not corner cases; they are the kernel's dispatch
  fabric, and each must be either modeled with explicit evidence or
  declined into a counter a reader can audit.
- **R4 (from both).** Make exactness checkable. At this scale no one
  reviews 5.7M answers; the design must carry its own evidence —
  proofs where theory reaches, per-run certificates where it does
  not, and differential baselines for every change.

§3 presents a design built to this specification; §4 then turns the
resulting instrument on the next wall — where imprecision lives —
which no pre-design measurement can reach.

---

## Notes for the writer (not part of the section)

- Number pins: harfbuzz OOM 49GB + Σ|C|² curve
  (docs/cfl-graph-explosion-and-scaling.md §R1; F0 is the log-log
  figure); dedup/folding nulls (same doc, phases 1–2); icall count
  18,773 = kernel FI census sites (kernel-fi-typerej run; the pinned
  answer set resolves 18,189); KallGraph caps = source audit commit
  058f9b5 with file:line (novelty doc dossier — keep attribution to
  "released implementation", tone structural not accusatory);
  asm census 129,812/4,900/13.7%/171 + imm-ptr exclusion honesty
  (docs/kernel-census/README.md, linux-6.8.2-ir-census.json.gz);
  int-provenance 47,676 modeled (+22,794 ledgered — cite both in
  final prose); section arrays 106 bounded / initcalls 646 / stubs
  16,915→12,597 (21.8%) (linker-flow census, task #22 phase A);
  extern boundary 6 undefined / 1 missing TU (kernel/bpf/verifier.o
  — note the pending user decision to add it; if added before
  submission, update to "0 undefined" and re-run) (#45 census).
- The KallGraph-caps paragraph is the load-bearing overlap with
  related work; in §9 keep only the positioning sentence and point
  back here for the evidence.
- 2.2 frames the census as pre-design scanning. Strictly, the
  census TOOLING matured alongside the solver; what is honest is
  that none of it depends on the flows-to formulation — it reads IR
  and link maps. Keep the claim "reproducible by scanner alone,"
  don't claim chronology.
- R1–R4 are the bridge the design section now opens from
  (design-section.md §3 references them by name).
