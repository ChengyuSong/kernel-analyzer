# Related Work (paper-ready draft, 2026-08-07)

Drafted against the paper outline §9 and the KallGraph dossier in
novelty-and-related-work.md. Citation keys are placeholders.
Target length ~1 page; cut order if squeezed: last paragraph first,
then compress the algorithmics paragraph into the engines paragraph.

---

**Type-based indirect-call analysis.** Function signature analysis
[FSA/IFCC, LLVM-CFI] and its multi-layer refinement MLTA [MLTA]
became the de facto kernel call-graph substrate, with successive
compensations — module-dependence pruning [TyPM], regional pointer
information for "simple" icalls [KELP], pointer-assisted layer
recovery [TFA], and strengthened layer maintenance [SMLTA]. Li et
al. [KallGraph] settled the standing of this line with an in-depth
study: MLTA's confinement and cast-propagation rules are unsound at
the design level, its fallbacks imprecise, and both defects are
inherited by every successor — over a hundred false-negative icalls
on defconfig Linux alone. We take that verdict as motivation rather
than re-litigating it, and add one forward-looking reason: under
LLVM opaque pointers the type signal that this entire line consumes
is eroding at the IR level. ORCFL uses type compatibility only as a
final filter on flow-confirmed candidates, never as the resolution
mechanism.

**Demand-driven and hybrid pointer analysis.** Demand-driven
CFL-reachability [HeintzeTardieu, SridharanBodik, ZhengRugina,
Boomerang] answers individual queries by exploring only relevant
graph regions, and hybrid designs [Das00, Unias] trade precision at
selected points for tractability. KallGraph [KallGraph] is the
strongest instantiation of this path for kernels: an on-demand,
history-aware traversal over the SVF PAG from each address-taken
function, with an object-level cast map, a byte-offset stack for C
interior pointers, type-based shortcut edges, and a bootstrapped
on-the-fly fixpoint, parallelized over 80 threads. We share two of
its conclusions — type-based resolution is not rescuable, and C
field sensitivity requires offset arithmetic rather than exactly
matched field parentheses (its per-path offset stack is the
demand-side dual of our whole-program Z_P shift residues). We
depart on how the cost of the underlying wall is paid. A call graph
is structurally hostile to per-query analysis: every icall is a
query, the queries share nearly all their work through a giant
may-alias structure, and resolution feeds back into every other
query, so on-demand becomes all-demands iterated to a fixpoint. The
released KallGraph implementation (commit 058f9b5) absorbs this
with resource caps the paper does not surface: traversals abort
beyond a 35-edge path length, the 50 most-visited nodes are
permanently blacklisted after every 20,000 deep visits, and formals
of functions with more than ~250 call edges per argument are
excluded up front. These caps fire precisely where kernel dispatch
flow concentrates — the type-erased hub that our anatomy shows
carries 93% of resolved pairs — so tractability is bought by
silently truncating the flows that are hardest to resolve, in the
region where fuzzing-based false-negative validation (8.9% icall
coverage) is least able to observe the loss. ORCFL is the
contrapositive design: keep the hub, measure why it forms, drain it
by certified constructions (answer-level identity channels with
completeness counters that must read zero; residues gated by proven
field-insensitivity equivalence), and pay the scalability debt once,
in the formulation, with every subsequent staging transformation
either machine-checked or certified per run. No resolution path in
ORCFL contains a silent budget.

**CFL-reachability engines.** A successful line of systems research
scales the CFL/Dyck closure computation itself: Graspan [Graspan]
as out-of-core edge-pair joining, POCR [POCR] and Pearl [Pearl] via
transitivity-aware solving, GraCFL [GraCFL] via cache-efficient
worklists, and most recently staged and restructured evaluation —
grammar staging [STG], skewed tabulation [SkewedPLDI24], relation
chaining [SQUID], sparse-matrix closure [FastMatrixCFPQ]. A sibling
line exploits client structure without changing the relation:
exact client-driven graph reduction [MoYe], context-aware summary
pruning [CAT], and reachability indexing for repeated queries
[FLARE]. Our saturation baseline builds on GraCFL, the strongest
of the engines on our graphs — and that is the point: these engines
are genuine successes at the engine level, and their success is what
isolates the residual wall as the formulation's output size. Over
LLVM-IR-scale graphs the pairwise alias closure is Θ(Σ|C|²) in the
a-connected component masses; an optimal engine reaches that floor
faster but cannot lower it (GraCFL exhausts memory on a single
library). Graph compaction does not help — the closure, not the
graph, is what explodes — a diagnosis we support with implemented
negative results (global dedup, RSM folding). ORCFL's
answer-anchored reformulation changes the output itself:
Σ|C|·(answer-relevant origins).

**Dyck-reachability algorithmics.** Chatterjee et al. [POPL18]
prove bidirected Dyck reachability optimally solvable by union-find
while the general problem is BMM-hard even at constant treewidth.
Our memory-join layer is their BidirectedReach rediscovered in a
production solver, and we cite it as such; what is new is the
composition — witness-exact unification beneath a directional
origin-fact propagation, proven lossless with respect to the CFL
relation (machine-checked), where the classical unification-below-
inclusion hybrid [Das00] sacrifices precision by construction. Our
field model places offsets in the weight domain (a Z_P quotient, in
weighted-pushdown terms [RSJ05]) rather than the parenthesis
alphabet, which cannot host container_of; KallGraph's byte-offset
stack is independent, contemporaneous evidence for the same
conclusion. Engineering components — difference propagation, wave
scheduling, online cycle elimination [PearceEtAl, WavePropCGO09,
Fahndrich98, HardekopfLin07] — are adaptations of Andersen's best
practice to CFL-plane granularity, not claims of novelty.

**Kernel modeling and soundness accounting.** Kernel call graphs
feed CFI policy generation [KCFI, IFCC, FineIBT], fuzzing target
reachability [Syzdescribe, StateFuzz], and static bug finding
[UBITect, others]; all inherit the substrate's soundness. Yet the
kernel's actual dispatch fabric routinely bypasses the IR channels
these analyses model: inline assembly (129,812 sites in our corpus,
13.7% pointer-capable), integer-laundered pointers (the ptrtoint/
inttoptr channel KallGraph itself identifies as the source of its
known false negatives), PREL32 linker section arrays (initcall
tables are module-level assembly, invisible to any PAG), and
patching families (static_call, tracepoints). We are not aware of a
prior kernel-scale system that models these boundaries under an
explicit accounting discipline — each channel modeled with
witnesses or declined into a ledger, with per-run closure
certificates discharging the solver model's assumptions — which we
argue is the missing methodology for call graphs that downstream
security mechanisms are asked to trust.

---

## Notes for the writer (not part of the section)

- The KallGraph cap claims MUST cite the released implementation
  (commit 058f9b5) with file:line — KallGraphAlgo.cpp:35 (path
  cap), :59-81 + :32-34 (dynamic blacklist), Util.cpp:107-115 +
  Util.hpp:4-6 (static blocking, baseNum=50). Keep the tone
  structural ("the demand-driven signature of the same wall"), not
  accusatory; their type-based study is cited approvingly in the
  same section.
- Do not make a head-to-head avg-targets precision claim in either
  direction (different kernels/configs/opt levels; their number
  embeds cap truncation, ours embeds the hub). If evaluation adds a
  comparison, run their binary on our corpus, diff both directions,
  and instrument the caps.
- Diligence: novelty doc §5 now carries the full 2026-08-30 survey
  triage (all five novelty claims survive; MoYe/CAT/FLARE are the
  must-cite client-structure neighbors; MCFL POPL'25 is the
  underapprox contrast; POPL'24 dynamic bidirected Dyck cited next
  to our incremental with fragment scoping). SQUID and
  FastMatrixCFPQ VERIFIED against PDFs in repo root
  (oopsla26-squid.pdf: PACMPL 10(OOPSLA1) Art.162, DOI
  10.1145/3798270; FastMatrixCFPQ.pdf: STTT/SOAP'26, DOI
  10.1007/s10009-026-00864-y). CAT = ICSE'26 page only, no paper
  retrievable 2026-08-30 — cite title/venue only, NO numbers, until
  the PDF appears. TnFix unverified, peripheral. STILL OPEN:
  group-weighted Dyck manual check; no 2026 KallGraph successor
  removing the caps.
- If asked "why not SQUID/FastMatrixCFPQ as the engine": same
  answer as GraCFL/POCR — the wall is closure output size (Σ|C|²),
  which a faster engine reaches sooner but cannot lower. Now
  concrete: SQUID's largest C/C++ graphs (SPEC CPU 2017 SVFGs) are
  ~1M edges; the kernel corpus is orders beyond that before closure
  even starts.
