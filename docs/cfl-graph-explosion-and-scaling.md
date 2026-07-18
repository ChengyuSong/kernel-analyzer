# CFL Graph Explosion: Diagnosis, Soundness Review, and Scaling Plan

Date: 2026-07-03.
Companion to [compositional-cfl-analysis.md](compositional-cfl-analysis.md).

This doc records the analysis of three questions:

1. Why does the LLVM-IR-based constraint graph explode (nodes, and edges added
   during solving), causing OOM even on small programs?
2. Is the compositional analysis sound?
3. What should we do next, given the constraints below?

Constraints adopted for the plan:

- Keep GraCFL as-is: exhaustive (all-pairs), parallel, no on-demand mode, no
  grammar changes. It is fast on graphs whose closure is sparse.
- Data-flow-based target resolution only. Type/signature matching is not
  trusted (opaque pointers, bad casts in real code), so scaling must come from
  the graph, not from a type-based fallback.

## 1. Why the graph explodes

### The memory mechanism: closure size, not input size

GraCFL stores results as a `ReachabilityMatrix`: per node, per label, a hash
set of reached nodes (`src/gracfl/include/utils/Reachability.hpp`). Memory is
therefore proportional to the number of *derived facts*. Dedup prevents
storing a fact twice; it cannot compress a dense relation. **The materialized
closure is a lower bound on memory for any exhaustive solver** — parallelism
and dedup do not help when the answer itself does not fit.

The dominant fact count is V. Under the grammar

```
M = -d V d
V = (M? -a)* M? (a M?)*
```

a single `a` edge and a single `-a` edge are each complete V derivations, and
`CFLEdgeBuilder::addAssignmentEdges` always inserts both directions. So **both
endpoints of every assignment edge are mutually V-reachable by construction**,
and `-a* a*` chains extend this across any assignment-connected region. M then
fuses regions that share a deref node. The V relation over the graph
decomposes into large "may-share-a-value" components; each node's V-set is
roughly its component, so total V facts are

```
sum over components of |component|^2
```

One 100K-node component is ~10^10 facts. This is the OOM. It also explains why
post-solve V-SCC compression achieves 30-70%: those SCCs *are* these
components.

### Why IR-level construction makes components enormous

GraCFL's benchmark graphs are variable-level, pre-cleaned (SVF/Graspan-style).
Our builder differs in four compounding ways:

1. **Node per pointer-typed SSA temporary.** Every GEP, bitcast, phi, select,
   and load result is a node joined to a component by an `a/-a` pair.
   Source-level graphs have one node per variable; IR gives one per
   *occurrence* (~5-10x), and every extra node enlarges some component.

2. **Field-insensitive GEP + one deref node per canonical pointer.**
   `visitGetElementPtrInst` wires `base -> result` with `a`;
   `getRepDerefNode` gives one deref node per canonical pointer. All field
   pointers of an object are V-fused with the base, all loads/stores through
   *any* field meet at one memory node, and M fuses every producer and
   consumer of the object into one component. Structs with many pointer
   fields and widely shared objects are the worst case.

3. **Global initializer collapse.** `processInitializer` folds an entire
   `ConstantArray`/`ConstantStruct` into one deref node. A 300-entry ops
   table becomes a hub with 300 function in-edges; everything touching that
   global joins one component containing all 300 functions.

4. **Pre-optimization IR.** If the input bitcode predates mem2reg/SROA, every
   local variable is an alloca with load/store traffic — `d/-d` edges and
   M-derivations for scalars that source-level graphs encode as plain
   assignments.

### Diagnostic experiment (run before investing further)

Union-find over just the `a` edges of the input graph (seconds, no solver);
print the component-size histogram and `sum(|component|^2)`. That number is a
lower bound on final V facts (M only fuses components further):

- If the top component is huge, the diagnosis above holds and the plan in §3
  follows.
- If not, the blowup is M-derivation churn instead, and the plan must be
  revisited.

## 2. Soundness review of the compositional pipeline

**Verdict: the core architecture is sound.** V-SCC quotienting is
edge-adding (a homomorphism), union-find boundary merging is edge-adding, and
CFL-reachability is monotone, so composed reachability over-approximates
monolithic reachability. The three self-loop fixes documented in
`compositional-cfl-analysis.md` were the correct repairs. The composed
iteration does wire actual-to-formal edges for newly resolved targets
(`icallarg: -> arg:/larg:`, vararg, and `ret -> icallret` in
`runCompositionalSolve`), so cross-TU parameter flow through indirect calls is
closed under iteration. libpng validation (0 missing edges vs monolithic) is
consistent.

Four findings, in decreasing severity:

### 2.1 Iteration caps can silently under-approximate (soundness hole)

- `kMaxCompIterations = 8` in `runCompositionalSolve`: if the summary-edge
  loop has not converged after 8 rounds, it stops without warning. A capped
  fixpoint is not a fixpoint: missing summary edges mean missing V facts mean
  missing callees.
- `kMaxPerTUIterations = 32` in `solveAndCompressPerTU`: warns and proceeds.

Per the project rule (no silent fallback), both should assert, or at minimum
set a hard "result not sound" flag propagated to the output JSON.

### 2.2 Field-store filter is unsound under partial knowledge

`fieldFilterAccepts` returns `false` when `funcFieldStores[F]` is *non-empty*
but lacks the callsite's field key. This is only correct if the map is
complete per function, but callback tracing is explicitly one-level. A
function whose address is stored directly somewhere (map becomes non-empty)
*and* registered through a 2+-level helper chain elsewhere is wrongly rejected
at the second site's callsites.

Fix: a per-function completeness bit. While building the map, if any use of
`F`'s address escapes classification (passed to an untraced call, stored
through a non-GEP pointer, ...), mark `F` unknown => always accept. This makes
the filter unconditionally sound instead of "sound if tracing is complete".

### 2.3 V-SCC merging precision claim is overstated (soundness unaffected)

The companion doc claims V-SCC members "have identical points-to sets" and
that V "is transitively closed". Two corrections:

- **V is not transitive.** The pattern `(M? -a)* M? (a M?)*` puts all `-a`
  steps before all `a` steps, so `a` followed by `-a` (common-*sink*:
  `z -a-> x <-a- y`) is deliberately excluded from V. But `computeVSCC` runs
  Tarjan over V-*edges*, so SCC membership is mutual reachability through
  V-chains — coarser than pairwise V. Concretely: `z -a-> x` gives mutual
  V(z,x); `y -a-> x` gives mutual V(y,x); Tarjan merges {z,x,y}, yet V(z,y)
  does not hold monolithically. Merging manufactures it — exactly the
  common-sink smearing the grammar was designed to exclude, and a plausible
  mechanistic source of the 14 extra libpng edges.
- Even genuine mutual V means "may share a value", not equal points-to sets.

Both effects only *add* facts, so soundness stands. The accurate statement is
"sound, with bounded extra smearing". If the extra edges matter, the knob is
restricting merging to pairwise-mutual-V cliques rather than chain SCCs.

### 2.4 Boundary completeness is argued, not enforced

The `func/arg/ret/vararg/glob/icall` inventory looks right for calls and
globals. Channels to audit:

- `GlobalAlias`: does a symbol referenced in TU A and defined via alias in
  TU B land in `Gobjs`/`Funcs` under the same GUID?
- `GlobalIFunc`: resolvers are handled locally by `collectIFuncTargets`, but a
  resolver may live in another TU.

A one-time assertion pass — "every ExternalLinkage value participating in any
CFL edge has a boundary symbol" — would convert the doc's Assumption 1 into a
checked invariant.

## 3. Scaling plan (keeping GraCFL exhaustive)

Ordering principle: constant-factor graph shrinking did not move the harfbuzz
OOM (global dedup ungating, RSM-guided folding — both tried, see
`cfl-scaling-plan` memory). The fix must shrink the *closure*, i.e. shatter
the V components. All steps below keep GraCFL unmodified.

### 3.1 Per-field memory nodes (headline change) — IMPLEMENTED 2026-07-03

> **Status + design correction.** Implemented behind `--cfl-field-buckets=K`
> (default 0 = off). The original claim below ("grammar stays a/-a/d/-d") was
> wrong: node-keying alone cannot be sound, because two *different* pointer
> expressions can address the same field of the same object, and only a
> matched-parenthesis derivation can connect their field cells. The sound
> design extends the *grammar data* (GraCFL solver code still unmodified)
> with bucketed field terminals `f<i>/-f<i>` plus a wildcard `fx`, and rules
> `Fld ::= -f<i> V f<i>` (the exact analogue of `M ::= -d V d`), `Mq ::= Fld`
> (`buildP2GrammarWithFields` in `Global.h`). Construction changes:
>
> - GEPs are decomposed into per-struct-level offset steps
>   (`decomposeGEPLevels`), so `&s->inner.f` matches `t = &s->inner; t->f`
>   across helper functions. Level byte offsets hash into K buckets
>   (collision = sound extra smearing).
> - Unknown-offset accesses (i8/scalar pointer arithmetic, ptrtoint round
>   trips, aggregate loads/stores, memcpy without layout, unions, container
>   helpers) fall back to an assignment edge plus a `fx/-fx` self-loop on the
>   base, which soundly absorbs field steps of any offset and nesting depth.
> - Global initializers route values into per-field cells
>   (`processInitializer` with `addrNode`), splitting the ops-table hubs.
> - V-SCC compression retains intra-SCC field-label self-loops (same reason
>   as the a/-a/d/-d self-loop bug fix in the compositional doc).
>
> Known precision gap (not a soundness gap): type-punned access paths with
> *different nesting shapes* (flat `f_24` vs nested `f_8·f_16` from different
> base pointers) do not match — the interleaved-Dyck undecidability tax.
> K=0 (field-insensitive) remains the conservative reference mode.
>
> **SOUNDNESS GAP found 2026-07-07 (`test/t_container.c`).** The
> nesting-shape mismatch is NOT merely a precision gap: on the kernel's
> dominant dispatch idiom it loses required callees. Minimal repro:
> intrusive list (`struct widget { pad; list_head link; fptr handler }`),
> store via `w->handler` (clean `f_16` step), call after traversal via
> `container_of`. At -O1 LLVM folds container_of+access into
> `gep i8, %member, 8` — a flat positive byte offset from the *middle* of
> the object. Matching store (container+16) with load (member+8, member =
> container+8) requires offset *composition* (8+8=16). Result: K=0 resolves
> 2/2 handlers; K=16 resolves **0/2** — in saturation AND flows-to. Three
> compounding causes: (1) constant scalar-typed GEPs (positive folded
> offsets and container_of's negative offsets alike) all take the wildcard
> fallback (`decomposeGEPLevels` rejects any non-zero first scalar index,
> even constant); (2) the fallback's fx loop sits on the *member*, and no
> grammar rule derives container alias from member alias — there is no
> upward `FldInv ::= f_i V -f_i`, though field-address arithmetic is
> injective so the rule is valid; (3) even FldInv can't match flat `f_8·f_8`
> against `f_16` — composition is the fundamental requirement. libpng/the
> smoke suite never exercise the pattern, which is why this shipped.
>
> **FIXED for saturation (2026-07-07)** by the shift-indexed valley
> grammar (`buildP2GrammarWithFields` rewritten): field steps are residues
> mod P (`fieldBucket` is now `offset mod P`, signed-safe, NOT a hash — 
> prefer prime P since offsets are 8-aligned), chains `Dn<c>`/`Up<c>`
> compose residues, `V ::= Up<a> Dn<a>` (exact shifts agree), `VX` covers
> the absorbing unknown-shift element (fx fallback, which is now sound
> as-is), `M ::= -d V d | -d VX d`. `decomposeGEPLevels` accepts constant
> scalar-typed offsets (both container_of shapes). Only net-zero V and VX
> are ever assembled — exact-mismatch pairs get no rule — so the closure
> partitions by shift rather than multiplying. `V` keeps its name; every
> consumer (presolve V'-SCC via GraCFL on the same grammar, snapshots,
> compositional) works unchanged. Validation: t_container 2/2 in every
> field config (was 0/2); libpng per-icall identical to K=0 across
> saturation fi/fs16 and flows-to fi; smoke 4/4. Cost on libpng:
> saturation fs16 6.5 s → 74 s (the composing closure is pricier).
>
> **Sound-grammar saturation OOMs harfbuzz** (P=13: out of memory at the
> 49 GB cap after 5 h 38 m, vs 2 h 32 m / 18.2 GB under the unsound
> grammar). The reading is exactly R1's thesis biting its own fix:
> GraCFL materializes every nonterminal, and the sound grammar's
> scaffolding — Dn<c>/Up<c> chain relations, one per shift — is
> V-sized × (P+1). Soundness didn't just admit more answers; it
> multiplied the scaffolding. Grammar-only sound field sensitivity on an
> all-nonterminal saturation solver is measured dead at harfbuzz scale;
> the viable paths are solver-side: the answer-anchored flows-to (which
> never materializes chains) with its VX-transitivity fixed via
> union-find + provenance clusters, and/or per-(object, byte-offset)
> memory nodes. Both are approved to touch the solver.
>
> Flows-to under the shift grammar: facts become (origin, shift) pairs,
> f-edges are shift transformers, cells join on exact fact (V) with
> (o,X)-to-(o,s) hub cross-links (VX). Container-sound (t_container 2/2)
> but blows up on real inputs (libpng >400 s vs 37 s): the hub *copy
> encoding* makes VX bridging transitive — (o,s1)-members exchange facts
> with (o,s2)-members through the shared X cluster, which the grammar's
> pairwise VX never does — smearing every cell toward all P+1 shifts and
> amplifying the per-cell join quadratic by ~(P+1)². Not a bug; an
> inherent limit of encoding non-transitive alias as copy connectivity.
> Next (user-approved to touch the solver): union-find clusters with
> provenance-separated fact classes instead of hub copies.
>
> Alternative (b) — per-(object, byte-offset) memory nodes on the
> Andersen side — remains open if the composed saturation closure proves
> too costly at scale.
>
> **Solver rework phase 1 (2026-07-08) — union-find + bit planes.** The
> flows-to core now merges exact-fact join clusters via union-find (same
> (o,s) => same abstract cell; no hub nodes, no k duplicated member fact
> sets) and stores facts as per-shift llvm::BitVector planes with
> word-parallel difference propagation. Two hazards found and fixed en
> route: (i) full re-dirty on merge caused a merge-cascade quadratic —
> split into a propagation delta (true new facts only, plus a one-time
> direct push of the merged set along the loser's moved edges) and a
> join backlog filtered by a per-class `joined` plane intersected on
> merge; (ii) list bloat on merged classes — compacted via find()+dedup
> when grown past a watermark. Results (identical per-icall resolution
> everywhere):
>
> - libpng: FI 144 ms, fs16 620 ms (hub version: 11.5 s / >400 s).
> - harfbuzz FI: **8 h 13 m → 4 m 56 s wall, 703 MB** (162x), same
>   330/2,795 resolution as the 8 h ground truth.
> - harfbuzz fs13 (prime P): **first sound field-sensitive result on
>   this input — 32 m 54 s, 1.27 GB**, 2,766 targets, a strict subset of
>   FI's 2,795 (29 spurious targets pruned; ICALL-diff verified). For
>   contrast: sound saturation OOMs at 49 GB; unsound saturation took
>   2 h 32 m / 18.2 GB.
>
> Remaining cost in fs13 is the VX smear (570M facts ≈ every root at
> most shifts on wildcard-touched classes).
>
> **Phase 2 (2026-07-08) — pairwise VX via bridges + 1-bit provenance:
> implemented, validated, and a clean negative result.** VX links became
> bridge edges (native facts cross as 'bridged'; bridged facts join and
> propagate normally — value flow launders provenance, mirroring the
> grammar where M-hops are separated by value steps — but never cross a
> second bridge). Outcome on BOTH libpng and harfbuzz: fixpoints
> identical to the phase-1 unions and zero residual bridged facts —
> load/store round trips legally launder everything, so the smear is
> licensed by the grammar, not an artifact of union transitivity. The
> 570M facts are the true cost of wildcard density. Machinery kept as
> the grammar-faithful encoding (free when wildcards are rare — the
> kernel case; ~20% on harfbuzz fs13: 40 m vs 33 m, same 2,766 targets).
> Consequence: further fs gains on C++ come from the ENCODING (fewer
> unknown-offset fallbacks: fieldwise memcpy expansion, container
> summaries via StructAnalyzer), not from the solver.
>
> **Encoding round (2026-07-08, committed b3a8843).** Wildcard census on
> harfbuzz: memcpy-unknown-layout 43%, ptrtoint-escape 31%, variable-
> offset GEP 15%, aggregate load/store 10%. Implemented per-residue
> copies for the memcpy/aggregate categories (sound with zero type info:
> byte copies preserve offsets mod P) — and measured them NET NEGATIVE
> on harfbuzz: C++ struct-assignment memcpys mint ~12k synthetic
> residue-cell origins and the resulting fact volume exceeds the
> wildcard smear it replaces (>646M facts and climbing vs 570M). Even a
> small-constant-length gate doesn't help — small struct copies ARE the
> dominant sites. Kept opt-in as `--cfl-residue-copies` for kernel
> evaluation, where fptr-bearing structs genuinely transit memcpy and
> the trade may invert. Lesson: fallback-elimination is not free
> precision — each eliminated wildcard adds origin-bearing structure,
> and on container-churn C++ the wildcard is the CHEAPER sound encoding.
>
> **LLM source-audit round (2026-07-08) — lacking ground truth, four
> Sonnet agents audited icall-callee pairs against the harfbuzz 13.2.0
> source (/data/csong/opensource/harfbuzz).** Results:
> - 29 FI-vs-fs13 pruned pairs: 25 verified CORRECT-PRUNE with file:line
>   evidence (unicode-funcs / cmap-accelerator callees correctly separated
>   from the match_func_t slot; these have pointer-compatible signatures,
>   so the type filter could never catch them — flow-earned precision).
> - **4-6 pairs = CONFIRMED fs SOUNDNESS BUG**: at the single
>   `would_match_input` instantiation, fs13 keeps ONLY match_coverage of
>   the ~7 legitimate match functions (match_glyph/match_class/
>   match_always/match_class_cached{,1,2} all stored into the same
>   ContextApplyFuncs/ChainContextApplyFuncs::match slots per source,
>   gsubgpos.hh:2558/2751/2797/4041-3). FI resolves all. Keeping coverage
>   while dropping glyph — same store mechanism — is internally
>   inconsistent. Localization so far: simple repros PASS
>   (test/t_ctxfuncs.c: struct-literal contexts, const-global + memcpy +
>   by-ref helper chain, both modes 4/4); a 145-function llvm-extract of
>   the real chain does NOT reproduce (both modes agree on the subset) —
>   the break is a full-module interaction. Next tool:
>   --cfl-trace-func=<name> to log where a function root's fact stops.
> - 12 sampled resolved pairs: 10 plausible, 2 measured false positives
>   (a cross-slot smear inside hb_unicode_funcs_t — the memcpy-wildcard
>   at work — and one paint-vs-shaper conflation).
> - 12 sampled type-matched-but-CFL-rejected pairs: 12/12 CORRECT-REJECT.
> Method note: agent auditing (~40 min wall, 4 parallel Sonnets) found a
> real soundness bug that all mechanical baselines missed — worth keeping
> in the validation loop.
>
> Known coarsening in the shift grammar (noted, unfixed): `DS0 ::= a | M`
> permits adjacent M-hops in chains, which the original valley grammar's
> `(Mq -a)*` shape forbade — a precision over-approximation, empirically
> free on libpng (per-icall identical to K=0). Restoring strict
> alternation would double the chain nonterminals.
>
> libpng validation (register merging also on): identical icall resolution,
> monolithic and compositional; V closure 8.0M -> 4.5M, M closure 275K -> 24K
> (11x).

Original rationale (see correction above):

- Key deref nodes by *(abstract object, byte offset)* instead of one deref
  node per canonical pointer. A GEP with constant offsets produces a distinct
  field-pointer node (not an `a` edge back to the base); loads/stores through
  it use the per-field deref node. `StructAnalyzer` + `DataLayout` provide
  the offset machinery (as in the field-sensitive Andersen side).
- Conservative fallbacks stay local: variable-index GEP, unions, offset
  overflow => collapse that access to the whole-object node. Degradation is
  per-access, not global.
- `processInitializer` gets the same treatment: initialize per-field deref
  nodes instead of collapsing whole ops tables into one hub. This removes the
  worst hubs and should also eliminate cross-field smearing among the 14
  extra libpng edges.

This is *not* the distrusted type matching: offset-based partitioning never
consults type names, only the byte offsets the code actually computes. Bad
casts just mean other code addresses the same object at the same offsets
(still unified correctly); opaque pointers are irrelevant because GEPs carry a
source element type and `DataLayout` resolves constant byte offsets.

Why it is the headline: it attacks explosion and imprecision in one change.
Mega-components exist because every field of a shared object funnels through
one deref node; per-field nodes shatter them, so `sum(|component|^2)`
collapses even though node count rises — feeding GraCFL a graph whose closure
is small enough to solve exhaustively.

Interaction: with field encoding, do NOT merge GEP results into the base
(they become field nodes). Still merge bitcast/addrspacecast results and
single-incoming phis into their operands (pre-solve unification of pure
copies; zero precision loss, removes nodes before the memory peak).

### 3.2 Function-pointer-relevance slicing

For callgraph purposes, drop constraint nodes for values whose type provably
cannot transitively carry a function pointer (`StructAnalyzer` knows which
types can). Keep `void*`/inttoptr conservatively — this uses types only to
prove impossibility, never to pick targets, so it is compatible with the
no-type-trust stance. Directly shrinks components.

### 3.3 Hierarchical composition

The standing answer to "no demand solving": compositional + V-SCC compression
bounds what the all-pairs solver ever sees at once. Compose in a merge tree
(TU -> library -> program), re-compressing at each level (compose -> V-SCC ->
export is already implemented), so no single solve sees the whole program.
Also improves incremental rebuild and caching.

### 3.4 Soundness fixes first

Items 2.1 and 2.2 are small, independent, and should land before any scaling
work so that eval comparisons stay meaningful.

### 3.5 Fallback, only if still OOM after 3.1-3.3

The pressure point would then be exactly one place: the final composed solve.
Only then consider demand-driven V queries (V is consumed at only ~|icalls|
fptr nodes plus allocator return nodes) or online mutual-V collapsing, scoped
to that single level — not a GraCFL rewrite. Expectation: the component
histogram moves enough under 3.1 that this is never needed.

## 4. Suggested sequence

1. Run the §1 diagnostic (a-edge component histogram) on harfbuzz to confirm
   the quadratic-component theory. Cheap; falsifiable.
2. Land 2.1 (caps -> assert/flag) and 2.2 (completeness bit).
3. Implement 3.1 per-field memory nodes (+ initializer split, + copy
   unification), validate against `test/libpng/eee13` baseline invariants and
   `test/eval-compositional.sh`.
4. Add 3.2 slicing if still needed; measure with the same histogram.
5. Re-evaluate harfbuzz; only then consider 3.5.

### 3.6 Generic constraint-graph cloning (design, 2026-07-03)

Cloning = inlining at the constraint-graph level. Like the compiler inliner,
it is generic for any C/C++ because selection is metric-driven, never
name/pattern-driven.

**Selection (per function F):**
- not in a call-graph SCC (no recursion; Tarjan over direct calls)
- pointer-moving (pointer args/ret or pointer-typed stores) — else skip
- template size |edges(F)| <= T (e.g. 64) after bottom-up composition
- rank by fusion score: callsites(F) x cell-traffic(F) (the s x l product
  the clone eliminates); spend a global edge budget top-down by score.
  analyzeHighDegreeNodes supplies the ranking signal.

**Mechanism (bottom-up over the clone DAG):**
1. Record per-function edge ranges during runOnFunction (like
   moduleEdgeRanges) => edge template per F. Bottom-up order composes
   templates like inlining; the size cap bounds composition.
2. At each direct callsite of a selected F (handleCall): instantiate fresh
   node IDs for all F-local nodes (formals, locals, ret, deref cells),
   remap the template, wire actuals->cloned formals and cloned ret->result.
   Non-local nodes (globals, non-cloned callees) keep original IDs.
3. Indirect callsites and cross-TU calls keep the shared original nodes
   (sound: original stays fully wired). Virtual/resolved-icall cloning is a
   later extension inside the fixpoint loop.
4. Heap cloning falls out: AllocSites inside a clone get per-clone opaque
   objects — the generalization of the allocator-wrapper special case.
5. Compositional: cloning is per-TU at edge-build time; boundary symbols
   remain on the originals, so composition is unchanged.

**v2 option:** instantiate compressed summaries instead of raw templates —
run per-function V'-quotient (reuse compressConstraintGraph) so a wrapper's
template is a handful of boundary nodes; much smaller instantiation cost.

Soundness: cloning only refines merging (each clone over-approximates its
own context; the union of clones covers the original's behavior); per-clone
allocation sites split, never fuse, may-facts.

## 4. Research agenda (2026-07-04)

Context: the literature's "CFL points-to is solved" impression rests on
post-analysis benchmark graphs (§"benchmarks" discussion) and Java
demand-driven systems. Raw IR-level PAGs (ours, and SVF's — student
reproduced the same blowups on SVF PAG) are an unaddressed instance class.
Five problems, ranked; R1 expanded as the concrete formulation.

### R1. Output-restricted CFL-reachability (ORCFL) — core problem

**Problem.** Given edge-labeled digraph G, normalized CFG with nonterminals
NT, a designated answer nonterminal A, source set S ⊆ N, sink set T ⊆ N:
compute A ∩ (S×T) with time/space parameterized by |E|, |answer|, and a
structural width of the instance — NOT by the closure cardinality of
scaffolding nonterminals. Standard saturation materializes every fact of
every nonterminal; for pointer grammars the scaffolding (value-alias V) is
quadratic even when the answer is tiny.

**Why the current formulation loses.** Andersen materializes pts-shaped
output (Σ|pts(v)|, rectangular). The V-based grammar materializes
alias-shaped output (≈ pts ∘ pts⁻¹, square). Σ|comp|² and the s×l cell
products measured on harfbuzz are the concrete face of that squaring. The
client reads V only at icall fptr nodes: the answer is rectangular
(Function sources × fptr sinks); the squaring is pure scaffolding.

*Caveat (important):* pts-shaped output is necessary, not sufficient.
Andersen itself does NOT scale on whole kernels (confirmed by prior
attempts here): when the abstraction collapses — field-insensitive cells,
context-insensitive wrappers, murky heap identity — pts sets themselves go
quadratic and Sigma|pts| approaches n*m, and propagation cost follows. Both
formulations die with a collapsed abstraction; the alias-shaped one just
dies squared-first. ORCFL is therefore paired with, not a substitute for,
the precision levers (fields, cloning, slicing, heap identity).

**Instance recast (flows-to form).** Sridharan-Bodík style:
  flowsTo ::= src ( a | put_f · alias · get_f )*
  alias   ::= flowsTo⁻¹ · flowsTo
Answer = flowsTo ∩ (S×T), S = address-taken Function nodes (+ alloc sites
for alias clients), T = icall fptr operands (or query roots). Key
observation: alias is *consumed* only at (store-ptr, load-ptr) pairs whose
accesses meet on a matching cell/field — a demand set D far smaller than
all-pairs, further restricted by S-reachability and T-co-reachability.

**Algorithm sketch to evaluate.** Bidirectional summary tabulation with
answer-directed scheduling: maintain S-anchored forward flowsTo facts and
T-anchored backward facts; form alias facts lazily as joins only when both
sides reach a common cell, store only alias ∩ D. Storage target:
O(S-reachable FT + T-co-reachable FT + |D|) — pts-shaped plus demanded
alias, never V. Degenerate cheap prototype: |S| is small (10^2-10^4
address-taken functions), so joint-frontier multi-source forward flows-to
alone ("fptr-flows-to mode", generalizing the slicer's taint pass from
components to derivations) bounds the answer without any V materialization.

**Positioning.** Magic-sets/query-directed Datalog gives the generic
transformation but reintroduces quadratic sideways bindings on alias
grammars; Sridharan-Bodík/Boomerang are per-query with refinement, not
exhaustive-answer with bounded scaffolding; GraCFL-style parallel solvers
are all-nonterminal saturation. The delta: show which structure of PAG
instances (bidirected a/-a, cell-local d-matching, mutual-V quotients from
R3) makes answer-directed tabulation effective, implement on a parallel
solver, evaluate on the R2 suite. Measurable hypothesis, testable today:
storage ratio V-facts / FT-facts ≈ Σ|alias-class|² / Σ|pts| (libpng: V
counts known; FT approximable by taint closure from Function nodes).

**v0 prototype results (2026-07-04, `--cfl-flows-to`).** Implemented the
degenerate cut: after presolve merge, propagate root ids (all no-in-degree
value origins + address-taken Function classes) forward over a-edges; two
cells join (bidirectional copy) when their parent pointer classes share a
root; answers read at fptr classes.

- *libpng:* precision exactly matches mono saturation — identical
  per-symbol callgraph counts, `Callee by type: total 27, match by CFL 9`,
  identical warning set. Storage: 192,784 root facts vs 7,475,876 final V
  edges (~39×); runtime same ballpark (~6–11 s CGPass either way).
  Rectangular-answer hypothesis confirmed on the well-conditioned instance.
- *harfbuzz:* **first CFL-based resolution to complete on this input** —
  8 h 13 m wall, peak RSS 1.67 GB (saturation OOMs at the 49 GB cap).
  Presolve: 95,332 nodes → 10,511 V' classes, Σ|class|² = 1.78B. Final:
  24,117 flows-to classes, 13,347 roots, 55.75M root facts, 40.4M hub-join
  edges, 17.55M worklist pops; resolved 330 icalls / 2,795 targets
  (`Callee by type: total 13231, match by CFL 2795`; address-taken 410,
  used 379 — no independent ground truth yet). Reading: storage stayed
  rectangular (55.7M facts ≈ 32× below the 1.78B V lower bound, 1.7 GB),
  so memory is solved; *work* is now the blocker — in the giant
  a-component every root reaches nearly every class, so propagation is
  ~|E|·|roots| ≈ 10¹⁰ (hence 8 h single-threaded). Confirms the caveat
  quantitatively: abstraction collapse, not closure shape, is the residual
  cost driver — per-field memory nodes (lever #1) attack exactly that, and
  the propagation itself is embarrassingly parallel/bitset-able if needed.

**Derivation slice (2026-07-05, `--cfl-flows-to-slice`).** 1-bit
bidirectional taint (forward from address-taken functions, backward from
icall operands) with memory jumps over Steensgaard classes (unification =
cheap sound over-approx of the shared-root join), closed under alias
evidence: touching a cell class keeps its cells and walks backward from
their parents, recursively — origins outside the source–sink flow must
survive because they justify joins (slicing derivations, not paths).
Near-linear; costs 0–15 ms.

- *libpng:* callee sets identical to unsliced flows-to; 572/720 classes,
  498/576 roots kept.
- *harfbuzz:* 14,089/24,117 classes (58%, 9,524 core), 11,003/23,689
  a-edges (46%), 8,674/11,688 cells kept — computed in 15 ms. Sliced
  solve: 8 h 04 m (vs 8 h 13 m unsliced — **no real speedup**), identical
  resolution (330 icalls / 2,795 targets; unused-address-taken and warning
  sets diff-identical). The decisive diagnostic: hub-join edges are
  40,420,490 sliced vs 40,426,616 unsliced — the slice removed the half of
  the graph that carried almost none of the work. Root facts only dropped
  55.7M → 45.6M. The cost lives in the entangled core the slice keeps *by
  definition*: ~20.2M (root × cell) registrations over 8,674 cells means
  the average kept cell's parent is reached by ~2,300 of the 7,938 kept
  roots. Lesson sharpened: on a collapsed abstraction the fptr-relevant
  core IS the giant component; pruning attacks |graph|, but the cost is
  the density of the core, and only field sensitivity (per-field cells
  shrinking the alias over-approx and shattering the component) attacks
  density. The slice remains nearly free (15 ms) and answer-preserving,
  so keep it as a standard pre-pass — its payoff should grow once
  per-field cells make the core sparse.

**Field-sensitive flows-to (2026-07-06/07).** Extended the flows-to solver
to consume the §3.1 field encoding (previously it required buckets=0).
The grammar's `Mq ::= M | Fld` symmetry maps directly: deref cells and
field-pointer results are *tagged children*; the join clusters are keyed
(root, tag) instead of (root); a fx-wildcard parent registers under a
per-root ANY cluster that is cross-linked to that root's bucket clusters
(links only between clusters that both have members). Nesting needs no
path tracking — joins cascade level by level like the grammar's
derivations. Validated on libpng with a new deterministic `ICALL` dump
(verbose≥2; earlier "identical callee set" diffs based on per-symbol
count lines were vacuous — those lines don't exist; re-verified for all
prior claims): saturation-fi == saturation-fs16 == flows-to-fi ==
flows-to-fs16 == flows-to-fs16-sliced, 9 icall pairs each.

- *harfbuzz:* field sensitivity made it WORSE — killed after >9 h at
  5.3 GB (FI: 8h13m, 1.67 GB). Cause measured, not guessed: 1,697
  wildcard (fx) nodes from C++ unknown-offset accesses (containers,
  memcpy, i8 arithmetic); at 1M pops already 64,610 wildcard
  registrations across 2,020 ANY clusters — i.e., 2,020 roots have their
  ~16 bucket clusters legally re-bridged. The wildcard fallback is
  semantically required (unknown offset must alias every field). BUT the
  attribution run corrects the first-draft diagnosis: field-sensitive
  *saturation* COMPLETES harfbuzz (2 h 32 m, 18.2 GB peak, V closure 295M
  edges, `match by CFL 2811`) where field-insensitive saturation OOMs at
  49 GB — so the encoding genuinely shatters the V closure despite the
  wildcards. The flows-to fs16 blowup is therefore specific to the
  cluster machinery (per-(root,tag) hub nodes duplicate root sets across
  22k+ hubs; 2× class inflation, presolve merges less: 10,511 → 15,785
  V'), fixable by the union-find cluster collapse. Caveat: all K>0
  numbers carry the §3.1 soundness-gap asterisk — the missing offset
  composition that loses container_of callees is also what keeps the
  closure this small; a sound composing encoding will grow it.
- Consequence for the plan: lever #1 is not unconditional. It should pay
  where unknown-offset access density is low (kernel-style C with
  explicit struct fields) and be neutralized where it is high (template
  C++). PHP unserialize (50 MB C, 146k classes, 96k roots, Σ|class|² =
  26.5B — far beyond saturation) is running as the C-side test.
  Remaining levers if wildcards dominate: reduce unknown-offset
  fallbacks at the edge-builder (fieldwise memcpy expansion via
  StructAnalyzer, container summaries), and the union-find cluster
  collapse + co-occurring-root dedup (join clusters are SCCs by
  construction; k co-occurring roots do k× redundant propagation work).

Implementation notes: (1) every access site has its own assistant cell, so
a pointer class carries many cells — the join must register all of them,
not one (v0 bug: single `cellOf` slot silently dropped all memory flow).
(2) The per-root cell clique linearizes to a hub node (cell ↔ hub_o)
with identical transitive closure — kills the |cells(o)|² edge blowup.
(3) Join copies are bidirectional, so joined cell clusters are de facto
union-find merges; a future solver can union instead of propagate, but the
#cells·#roots registration bound stands.

### R2. Honest raw-PAG benchmark + instance-hardness metrics
Release raw PAGs from two independent builders (KAnalyzer, SVF) with the
hardness metrics (component histograms, Σ|comp|², label vocabulary census,
cell-traffic distribution, chain depth) and show the frozen `.g` suites and
raw PAGs are different instance classes. Measurement paper + artifact.

### R3. Quotient solving with a precision theory for non-transitive V
Online mutual-V collapse during solving (CFL analog of online cycle
elimination); open theory: chain-SCCs over-merge because V is not
transitive (§2.3) — when is quotienting precision-preserving, and what does
common-sink smear cost on real code?

### R4. Sound field sensitivity on raw IR under opaque pointers
The per-level decomposition + wildcard-absorption encoding (§3.1) as a
practical point between field collapse and undecidable interleaving, with
an honest type-punning gap characterization. Evidence in hand.

### R5. Closure-predictive selective context sensitivity
Cloning budgeted by predicted closure reduction (fusion score, §3.6) vs
uniform k-limits — introspective context sensitivity for CFL-over-PAG.

## 5. Factored closure representation (FRI) — design sketch for a new solver

Target: compute P2(+fields) closure with space linear-ish in graph size,
never materializing pairwise scaffolding. Motivated by the measured
structure of V: cliques (mutual-V components) + bicliques (per-cell
store x load products) + transitive chains. All three have linear factored
representations; only their extensional pairing is quadratic.

### The factorization theorem (informal)

In P2, V = (Mq -a)* Mq (a Mq)*: every -a step precedes every a step, with
identity splices (M/Fld) between. So every V-derivation has valley shape:

  V(x, y)  <=>  exists pivot chain p1 ≡ p2 ≡ ... ≡ pk (Id-edges) with
                x in DownReach(p1)  and  y in UpReach(pk)

where Down-steps are (-a) edges, Up-steps are (a) edges, and Id-edges are
the identity nonterminals: M between cells of V-related pointers, Fld
between same-bucket field nodes of V-related bases. Each pivot p thus
*generates* the rectangle DownReach(p) x UpReach(p) ⊆ V. V is exactly a
union of pivot-generated rectangles — store the generators, not the pairs.

### Representation: three layers

1. **Quotient (union-find).** Nodes collapse when mutually V-related; all
   other layers operate on class reps. Precision knob (see §2.3): chain-SCC
   collapse (coarser, cheap — subsumes the presolve merge, done online) vs
   pairwise-mutual-only (precise, costlier). Soufflé's `eqrel` is the
   precedent that this layer alone is a big win for equivalence-heavy
   relations.

2. **Pivot graph.** Nodes: classes, cells (deref nodes), field nodes.
   Edges: a/-a between classes (Down/Up steps); Id-edges inserted by rule
   firing:
     M-rule:   cells c1,c2 with parents P1,P2:  V(P1,P2)  => Id(c1,c2)
     Fld-rule: field nodes at same bucket with V-related bases => Id(f1,f2)
   V(P1,P2) is *queried* (layer 3), never stored. The solver's fixpoint is:
   insert Id-edges whose guard holds, until none fire. Facts live as edges
   of a small graph, not tuples of a big relation.

3. **Reachability index over the pivot graph.** Down*/Id/Up* queries are
   plain reachability on the pivot graph (with the valley discipline:
   Down-phase, then Id/peak, then Up-phase — a 3-state NFA product, still
   single-relation reachability). Maintained incrementally under Id-edge
   insertions: interval/tree/chain indices (POCR's spanning trees are the
   precedent for factored transitive structure). Worst case is incremental
   transitive closure — not free, but on a graph of #classes + #cells
   (harfbuzz: ~15K after quotient, vs 10^9+ pairwise facts).

### Answer extraction

Callgraph: for each icall class t, enumerate function classes s with
valley-reachability s ~> t — output is the rectangular answer directly.
Aliasing: V(x,y) is a single reachability query; pts-style sets enumerate
one rectangle at a time. Nothing pairwise is ever materialized unless a
client asks for it.

### Why this can work where saturation cannot

Saturation cost >= closure cardinality (Sigma cliques^2 + Sigma s x l).
FRI cost = pivot-graph size + #rule firings + index maintenance; the
quadratic objects exist only as (generator, reachability) pairs. The
open risks, honestly: (a) incremental reachability maintenance can degrade
under dense Id-insertion waves (the a x M cascade reappears as Id-edge
churn — but each cascade level is ONE Id-edge here, not s x l facts);
(b) the precise (non-chain-SCC) quotient needs a pairwise-mutual test that
is itself a reachability query — chicken-and-egg handled by starting coarse
and refining, or accepting chain-SCC precision (= current compositional
compression, empirically +14 edges on libpng).

### Precedents to position against

- Soufflé `eqrel` (union-find-backed relations): layer 1 exists in Datalog
  engines; FRI generalizes to Dyck-generated rectangles.
- BDDBDDB (Whaley/Lam): BDDs = generic factored relations; fragile variable
  ordering. FRI is the domain-specific, predictable version.
- POCR/Pearl spanning trees: factored transitive closure for one
  nonterminal; FRI extends factoring to the mutually recursive V/M system.
- Valiant / BMM: rectangle composition (U1 W1^T)(U2 W2^T) = U1 (W1^T U2) W2^T
  is the algebraic core — factor-level joins, small middle products.

### Validation plan

1. Exact-answer equivalence vs GraCFL saturation on libpng (ground truth
   captured: V counts, 27/9 tallies, per-icall targets).
2. harfbuzz full-stack graph (26,317 nodes / 84,354 edges — the instance
   that defeats saturation at 25+min): target = complete solve, report
   pivot-graph size, Id-edge count, peak RSS.
3. Ablations: quotient-only (= presolve merge), + pivot rectangles,
   + incremental index. Each layer's contribution isolated.
4. SVF PAG cross-check (student's second builder) for generality.

## 2026-07-11: would_match_input soundness bug — two root causes, both fixed

The audit-flagged harfbuzz fs13 miss (`would_match_input` kept 1 of 30
pairs) decomposed into two independent, mode-independent identity losses
in the closure relay (`RuleSet::would_apply` → `$_21`/`hb_map` →
`operator|` → `hb_map_iter_factory_t::operator()` → `hb_map_iter_t`):

1. **Aggregate call args/returns dropped** (`handleCall`,
   `removeCallEdges`, single-callsite dedup): actuals and return types
   were gated on `isPointerTy`, so first-class `{ptr,ptr}` aggregates —
   exactly how clang returns 16-byte closures/factories by value —
   created no actual→formal / return→callsite edges.
   `visitReturnInst`/load/store already used `containsPointerType`; the
   call boundary now does too. Regression: `test/t_aggrelay.c`
   (0/2 → 2/2 in K=0 and K=13).

2. **Flows-to root minting dropped merged origins**: roots were minted
   only for classes with no incoming a/f edges (`!hasIn`). Presolve
   copy/field merges (memcpy modeling) can union an alloca's class with
   in-edged nodes (this-spill reloads), after which the alloca is never
   minted and the object's identity is erased — visible in traces as an
   alloca whose class has zero facts (not even its own seed). Now any
   class containing an alloca / GlobalVariable / alloc-site value is
   minted regardless of in-degree.

Result: harfbuzz fs13 = 2808 pairs, exactly == FI (would_match_input
30/30); libpng all-config parity unchanged; smoke 4/4; t_container 2/2.
Cost: roots 13,025→13,376, facts 277M→745M (2.7×), fs13 runtime
33m→67m. Note fs13 now buys zero final-answer precision over FI on
harfbuzz (template C++ + wildcard smear); the fs payoff hypothesis
lives on kernel C.

### Open: coredump.bc sysctl proc_handlers (21 pairs) — external-boundary identity split

NOT residue arithmetic: both sides compute `sysctl_entry` at s7. The
write goes through the `new_inode()` return phantom (r727), the read
through the `file->f_inode` load phantom (r884); only external VFS code
connects the two objects. ft-FI and **saturation fs13 both resolve**
(via conflation / universal-node conservatism); flows-to fs13 cannot —
its cells are keyed by exact (origin, shift) and no in-module pointer
ever carries both origins. Bridge-semantics experiment (VX bridges →
phase-1 unions) changed nothing. Fix requires an explicit
external-boundary policy for flows-to (e.g., unify phantom objects that
cross the same external interface, or a bounded universal blob) — a
soundness/precision design decision, deferred.

## 2026-07-11: root co-travel measurement (`--cfl-cotravel-stats`)

Sizing diagnostic for root bundling (one plane bit per bundle of roots
with identical (class, shift) incidence). Zobrist set-hashes over final
R planes, exact-equality lower bound:

| input        | facts | active roots | distinct columns | fact compression | max bundle |
|--------------|-------|--------------|------------------|------------------|------------|
| libpng FI    | 17.1k | 585          | 259              | 2.8x             | 327        |
| harfbuzz FI  | 35.0M | 12,516       | 7,470            | 8.8x             | 4,707      |
| harfbuzz fs13| 770M  | 13,376       | 7,225            | **10.5x**        | **5,653**  |

Reading: 42% of all fs13 roots share ONE identical incidence column —
the "entangled core" (R1: every root reaches ~every class) is made of
roots the analysis literally cannot distinguish, so solving with one
representative per bundle is lossless there. Secondary: ~60% of classes
duplicate another class's full fact set (row hash-consing, ~2.4x,
composes with bundling). Both numbers are exact-equality lower bounds;
dynamic bundling (start merged, split on divergence) should exceed
them. Also fixes the GPU question's matrix width: ~7.2k columns
post-bundling. Conclusion: bundling is a confirmed >=10x lever on facts
(memory AND propagation work) — build it before considering GPU.

## 2026-07-12: solver profile + 19x FI speedup (commit 3e7a512)

`--cfl-solver-profile` (rdtsc phase accounting; perf is locked down on
this box) before any optimization:

- harfbuzz FI: join sweep = 94.9% of solve — 8.4B cluster lookups for
  35M facts. Cause: each fact swept the raw cellsOf list (~240 stale
  entries aliasing 1-2 live reps). NOT the plane ORs, NOT the hash map
  per se.

Fixes: (1) dedup cellsOf to live union-find reps at sweep start + after
the first fact of each sweep (which provably merges all cells of that
(class, shift)); (2) persistent scratch planes in addBits /
addBitsBridged / wflag (heap churn was ~29k cycles per addBits).

Results (identical resolution everywhere): harfbuzz FI 1275s -> 66.5s
(19x), fs13 67min -> 37min (1.8x — fs13 is fact-volume bound across 14
shift planes). Post-fix profile: a-prop = 88%, ~21k cycles per addBits
over ~200-word planes = cache-miss bound on ~235MB of scattered planes.

Implication for root bundling (task #10): implement as INTERNED SHARED
planes, not just narrower ones — the entangled-core classes hold the
same fact set, so one physical plane serves thousands of classes;
subset checks become pointer equality and the working set collapses
into cache. Width reduction alone (13.4k -> 7.2k roots) would only buy
<2x on the OR path.

## 2026-07-13: dynamic a-SCC collapse (commit 6d85667)

The SCC census (added to `--cfl-cotravel-stats`) showed the entangled
core is ONE dynamic SCC of 3,629 classes over shift-preserving edges
(a + residue-0 f), holding 1/3 of all a-edges. Mutually-reaching
classes receive each other's every fact, so their planes are equal at
fixpoint; merging them mid-solve (Tarjan every 256k pops, existing
merge()) is precision-neutral, dedups the core's planes to one copy,
and removes its internal delta churn.

Cumulative solver-round results (identical resolution everywhere):

| run          | before round | after |
|--------------|--------------|-------|
| harfbuzz FI  | 1275 s       | 33.8 s (38x) |
| harfbuzz fs13| 67 min       | 25 min (2.7x) |

fs13's residual entanglement is glued by shift-CHANGING f-edges and VX
bridges, which cannot be SCC-merged soundly (planes differ by rotation
/ provenance). Attacking that needs the interned-shared-planes
representation (or bundle-aware rotation), still queued as the bundling
task. Kernel-scale outlook: FI at 34 s for a 24.5k-class module makes
the whole-kernel FI run plausible without further work; fs13 wants one
more representation round.

## 2026-07-14: whole-kernel FI attempt #1 — stopped at 25h, diagnosis complete

First whole-kernel flows-to run (2,618 modules, FactSet planes, one-pass
binary predating the fixpoint/TopClass/closure-checker). Stopped
deliberately at 25h; log preserved at ~/kernel-fi-attempt1-partial.log.
State at stop: 218M pops, 1.40B facts, 212k clusters, 115k merges,
19.6GB RSS — memory comfortable, convergence tail unbounded in practice
(facts +40M/h, merges still active at hour 25).

What it established:
- FactSet planes hold kernel scale in memory (the dense-plane OOM is
  gone; 333k roots, 1.4B facts, under 20GB).
- The wall is merge-churn convergence, not memory and not per-fact cost:
  115k merges (harfbuzz needs 6.3k) with cluster coalescing still active
  at hour 25 — the intrusive-container / type-erased-hub / allocator-
  wrapper webs as predicted.

Plan for attempt #2 (in order):
1. Merge-churn fixes first: extend ContainerFuncs/AllocFuncs coverage
   over kernel registry APIs and alloc wrappers (kmalloc_wrapper yaml),
   and cut the merge -> full-backlog re-offer cost (delta-precise
   re-offers or interned planes).
2. Iterate on a SUBSET bclist (~200-400 modules, e.g. fs/ + kernel/ +
   mm/) to get TopClass culprit names, ClusterTrans, and rank census in
   ~1h loops instead of days.
3. Full 2,618-module rerun with --cfl-verify-closure + TopClass + the
   outer fixpoint, once subset iteration converges on the churn fixes.

## 2026-07-15: delta-precise merge re-offer — NEGATIVE result (reverted)

Implemented and validated (closure-certified, identical resolution on
all inputs): cell-rep unification queue + joined-mark union + cell-
parity-only re-offers. Volume metrics collapsed exactly as designed on
the kernel subset — re-offered facts 121M -> 5.9M (20x), sweep offers
35M -> 6.9M, join merges 18.3k -> 6.6k. Wall time nevertheless REGRESSED
26% (kernel subset iter0 299s -> 377s; harfbuzz FI 42s -> 54s).

Profiler post-mortem: the join phase those volumes live in was only 14%
of cycles; a-prop (76%) GREW 29% because eager cell unification forms
the mega-cell class early, and every subsequent fact delta fans out
over its concatenated load-edge list, versus the old lazy order where
cells absorb facts separately and merge later with bulk one-time
pushes. Lesson recorded: optimize where the cycles are, not where the
bookkeeping volume is — the cycle profile said a-prop throughout.

Consequence: the generic time lever for both harfbuzz fs13 and kernel
is the a-prop representation (interned/shared planes, delta-narrowed
ORs — task #10), not join bookkeeping. Merge machinery stays as
committed (4788d33 state).

## 2026-07-15: PHP unserialize completes — first full sound run

`unserialize.0.0.preopt.bc`, flows-to FI with outer fixpoint and closure
certification: 4 iterations x ~58 min (3.9h total), 3.5GB peak RSS,
closure verified on every iteration. Resolved 2,311 icalls / 395,639
targets; 197M final facts (the pre-solver-work estimate was 1.6B).
Historical context: saturation never completed this input, and the v0
flows-to prototype was deferred after partial 8h+ attempts.

Reading: 171 avg targets/icall says FI is coarse on the zend handler
tables — field sensitivity plus the filters are the precision lever
here, not more solver speed. The 4x iteration cost (re-solve from
scratch per fixpoint round; iteration 1 wired a genuine 77,610 pairs)
makes incremental cross-iteration solving the next-best generic time
win after the a-prop representation.

## 2026-07-15 (later): content-addressed delta blocks — second a-prop negative (reverted)

Tried: per-plane incremental Zobrist hash of dirty content; popped dense
deltas carry a content id; per-(class, shift) ring of absorbed ids gives
O(1) skip for identical re-arrivals. Correct (closure-certified,
identical resolution), but skip rate only 8.9% (kernel subset) / 11%
(harfbuzz) and the per-insertion hash-fold pass made runs 10-15% SLOWER
net. Root cause of the low hit rate: content identity is temporally
brittle — by the time another predecessor re-emits "the same" core
block, its dirty has drifted by a few bits, so hashes no longer match.
Dynamic content-addressing cannot capture co-travel; co-travel is an
END-STATE property (the co-travel census measures the fixpoint), not an
in-flight one.

Standing conclusions for the a-prop wall after two reverted attempts:
1. In-flight dedup tricks (id caches, delta-precise re-offers) do not
   pay: the cycles are memory-bandwidth on full-width plane ops, and
   arrival contents drift.
2. The structural levers left are: (a) parallelization — the plane ORs
   are embarrassingly parallel and bandwidth spreads across cores
   (task #11); (b) static width reduction if a sound PRE-solve root
   grouping exists (open); (c) fewer rounds via scheduling (topological
   pop order on the condensed a-DAG so classes pop once per wave).
3. Scheduling note from the data: pops process shifts round-robin per
   class; a topological order would turn the mega-set's diffusion into
   one wave instead of many partial arrivals — worth measuring before
   parallelizing, as it also reduces the drift that defeated (this)
   block dedup.

## 2026-07-16: topological wave scheduling — the a-prop lever found (commit 336440d)

Third attempt on the a-prop wall succeeded, and it was pure access
ORDER: static Tarjan condensation of the initial a/f graph assigns
topological ranks; the worklist drains as rank-sorted waves (pushes
land in the next wave). Deltas flow downhill; each plane is touched
~once per wave with its full accumulated delta, converting the
cold-miss scatter (76-88% of cycles) into ~one streaming pass per wave.
Pop order does not affect the fixpoint; ranks are only a heuristic.

Measured, identical per-icall resolution + closure certificates on all:

| input          | solve before      | solve after       | speedup |
|----------------|-------------------|-------------------|---------|
| harfbuzz FI    | 42 s/iter         | 2.1 s/iter        | 20x     |
| harfbuzz fs13  | 74 min total      | 6.7 min total     | 11x     |
| kernel subset  | 280 s/iter        | 12.5 s/iter       | 22x     |
| PHP unserialize| 232 min total     | 6 min total       | 39x     |

Pops collapse accordingly (harfbuzz FI 4.1M -> 69k; 37 waves). The two
reverted in-flight dedup attempts and this result together make the
diagnosis airtight: the cost was never redundant WORK, it was
fragmented ORDER. Cumulative solver history, harfbuzz FI one-pass:
1275 s (pre-July) -> 2.1 s = 600x, all generic, all certified.

Arena layout (spatial locality) not yet needed — order alone removed
the wall; keep as a card if parallelization exposes bandwidth limits.
Whole-kernel attempt #2 launched (expected ~hour-scale vs the 25h+
unbounded attempt #1).

## 2026-07-16: whole-kernel FI CONVERGES — first full-kernel sound run

Attempt #3 (after the on-demand allocator-callsite-node fix, 4133e31)
completed on the full 2618-module bclist (linux-6.8.2), FI flows-to,
5 outer iterations to fixpoint:

- **14,799 icalls resolved, 5,107,435 (callsite, callee) pairs**;
  iteration 4 wired 0 new pairs (converged, not capped).
- Solve: 291/214/240/216/215 s per iteration = **~19.6 min total
  solve**; 13-14 waves, ~375k pops, ~1.46B native facts, 393k classes
  / 321k roots after merges, 0 VX bridges (FI). RSS ~12.4 GB.
- Precision vs type-based: type matching admits **52,845,869** pairs;
  CFL confirms 4,879,335 of them — **~10.8x tighter**. Fan-out: median
  bucket 21-100 targets/icall (7131 sites), avg 345, max 4756; 851
  sites >1000 (dominated by known conflation: shared heap identities,
  static_call not yet modeled, mm page identity).
- PrintfSink: 9925 benign vararg callsites sunk (21,442 tail args
  unwired); 10,354 non-constant-fmt + 25 non-benign kept (sound).
- Wall time was NOT solve-bound: after convergence the run spent hours
  in log diagnostics — 5.1M ICALL lines plus the unused-address-taken
  check (O(|AT|x|callsites|) scan + full global-initializer dumps,
  12,842 warnings, multi-GB). Fixed in a7d9cff: ICALL dump now behind
  `--cfl-dump-icalls`, flattened callee set for the AT check, User:
  dumps at verbose>=3. Next full run should be ~40-50 min end to end.
- Artifacts: /tmp/kernel-full3-icalls.sort.gz (sorted pairs, 37 MB),
  /tmp/kernel-full3-stats.txt (per-iteration stats).

Compare attempt #1: 25h+ with no convergence in sight. Wave scheduling
is what made whole-kernel tractable. Next levers: parallelization
(task #11, bulk-synchronous supersteps), then kernel-specific modeling
(static_call, seq_open wrappers, page identity) for the >1000 fan-out
tail.

## 2026-07-17/18: solver parallelization (--cfl-solver-threads, a7b54b6)

Bulk-synchronous wave phases: rank-sorted waves drain in rank-contiguous
blocks (--cfl-solver-block, default 8192); within a block, bridge/
wildcard/a/f propagation runs data-parallel (per-class spinlocks on
foreign-plane writes, frozen union-find with read-only find, per-thread
contexts flushed at barriers); joins run as a sequential sub-phase per
block using the unchanged in-sweep code path. At T=1 the solver is the
old algorithm exactly (joins fused per class visit).

Two designs tried and REJECTED before landing on this:
1. Separate parallel join-filter pass (filter probes + deferred
   requests): doubled per-wave streaming traffic — join 1.8B -> 6.5B
   cycles on harfbuzz even after restoring the cells-dedup micro-opt.
2. Deferred per-fact join requests with a batched 3-pass apply (seq
   heads / parallel confirms via a sharded cluster registry / seq
   leftovers): first-offer facts re-touched cold at ~5x cycles; on the
   kernel subset merge churn ballooned to 3M deferred requests / 21B
   apply cycles and T=8 LOST to T=1. Lesson: the join sweep's value is
   that it runs while the fact's planes are hot; any deferral pays the
   full cold-miss chain again.

Measured (identical per-icall + closure certificates at T=1/8/16 on
libpng FI+fs13, harfbuzz FI+fs13 vs pinned baselines, all micro tests;
smoke 4/4; T=1 == pre-parallelization performance):

| input           | T=1        | T=8        | speedup |
|-----------------|------------|------------|---------|
| harfbuzz FI     | 2.34 s/iter| 1.29 s/iter| 1.8x    |
| harfbuzz fs13   | 6.7 min    | 2.7 min    | 2.5x    |
| kernel subset   | 7.7 s/iter | 5.5 s/iter | 1.4x    |
| WHOLE KERNEL T16| 215-290 s  | 430-450 s  | 0.5x — LOSS |

Whole-kernel T=16 REGRESSES (and RSS 12-14 -> 27.2 GB): at 333k roots
the dense planes are 41.6KB, propagation is bandwidth-bound, and locked
ORs into hot hub classes serialize + ping-pong plane lines across 16
cores; per-thread malloc arenas inflate RSS. fs13 scales BEST because
its work spreads over 14 shift planes with VX bridges (less hub
contention). Joins are the Amdahl wall everywhere (kernel subset: 63%
of cycles, sequential).

Guidance: use --cfl-solver-threads=8 for library-scale and fs inputs;
whole-kernel stays sequential until (a) target-partitioned exchange
replaces locked scatter ORs (each thread owns a class range, deltas
routed via per-thread outboxes — kills both contention and coherence
traffic) and/or (b) joins parallelize (concurrent union-find + batched
plane moves). T=8 + MALLOC_ARENA_MAX run pending to separate contention
from arena bloat.
