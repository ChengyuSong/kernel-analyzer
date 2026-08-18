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
plane moves). Follow-up (2026-07-18): whole-kernel T=8 with
MALLOC_ARENA_MAX=4 still runs 390-430 s/iter — the loss is lock
contention + bandwidth on hub planes, not malloc arenas. Parallel
verdict final for now: use threads up to library/subset scale only.

## 2026-07-18: incremental cross-iteration solving — WIN at library scale, NEGATIVE at whole-kernel (a6896d0, opt-in)

Sequential-performance lever after the parallel round: the outer
fixpoint re-solved from scratch each iteration (kernel: 5 x ~215 s
where iteration 4 wires 0 new pairs). Implementation: the fixpoint
loop moved inside runFlowsToResolution — resolution's newly appended
EB edges are translated in place (dense-id growth for new nodes),
seeded from the existing planes, new cells re-offer with cleared
joined marks, and the drain continues from the reached fixpoint.
Obsolete identity roots (pure no-in mints that gain callers — exactly
what a rebuild stops minting) are PARKED: masked out of new-edge
seeding; the closure verifier exempts parked bits on C1/C2.

Results (per-icall identity + closure certificate per drain at
library scale):

| input          | from-scratch | incremental | facts        |
|----------------|--------------|-------------|--------------|
| libpng         | identical    | identical   | flat         |
| harfbuzz FI    | ~7 s         | 3.3 s (2.1x)| 35.0->36.0M  |
| kernel subset  | ~31 s        | 27 s (1.15x)| 33.8->65.4M  |
| WHOLE KERNEL   | ~18 min      | ~82 min     | 1.44->4.09B  |

Whole-kernel is a hard NEGATIVE on two axes:
1. TIME/MEMORY: iteration-1 drain alone took ~43 min; facts 2.8x, RSS
   30 GB. Cause is structural: every wired formal materializes a COPY
   of the union of its callers' planes. From-scratch avoids this by
   re-running presolve copy-merge on the grown graph (single-in
   actual/formal chains collapse into one class). 829k wired pairs x
   dense caller planes at kernel scale = +2.9B facts. Parking removed
   the obsolete-root spread (103k roots parked) but not this.
2. ANSWER DISCREPANCY (open bug): converged at 14,780 icalls /
   5,090,540 pairs vs from-scratch 14,799 / 5,107,435. Fewer pairs =
   soundness-affecting. Prime suspect: a pure no-in root whose class
   LATER becomes an allocation site gets parked when it gains an
   in-edge, killing the heap object's identity (mintRoot no-ops since
   the class is already a root, but that root is parked). Subset and
   harfbuzz converge identical, so the interaction needs kernel-scale
   allocator wiring to manifest.

DISPOSITION: opt-in via --cfl-flows-to-incremental (default OFF =
exact previous from-scratch behavior, revalidated). Structural
follow-ups if incremental is to reach kernel scale:
- shared/COW planes or plane interning (kills the duplication AND is
  the standing fs13 lever);
- incremental single-in copy-merge at wire time (only safe when the
  formal can never gain a second caller — needs a retirement story);
- unpark-and-reseed when a parked class becomes origin-bearing (fixes
  the discrepancy suspect).

Sequential-performance scoreboard after this round: from-scratch
whole-kernel remains the production configuration (~18-20 min solve,
5 iterations); the next generic levers on it are plane interning/COW
(join+memory), delta-precise merge re-offers (join, worth re-testing
now that join is 63% of kernel cycles post-wave-scheduling), and
static_call modeling (task #14) to shrink the graph itself.

## 2026-07-18: answer-relevant root measurement (--cfl-root-relevance) — the demand-driven door is OPEN

Motivation: solver work scales with |E| x |roots|; kernel mints 333k
roots. How many does the ANSWER need? A root can influence resolution
only as (a) a function root read at an icall plane or (b) a merge
witness — joins are the only consumer of individual bits; a-prop is
blind unioning. So: log the (root, keeper) of every join-triggered
merge, compute fptr-ancestor classes (reverse a/f + bridges over the
final quotient), and report {function roots} ∪ {witnesses of
ancestor merges} — a SUFFICIENT set to replay this run's answers.

| input         | roots minted | sufficient    | fact mass | ancestor classes |
|---------------|--------------|---------------|-----------|------------------|
| libpng        | 584          | 177 (30%)     | 36%       | 192/357 (54%)    |
| harfbuzz FI   | 12,233       | 1,653 (13.5%) | 10.3%     | 5,651/18,112 (31%)|
| kernel subset | 62,929       | 9,288 (14.8%) | 21.5%     | 5,030/59,699 (8.4%)|
| whole kernel  | 321,484      | 74,052 (23.0%)| 30.2%     | 47,791/262,916 (18.2%)|

Whole kernel (2026-07-19, resolution identical 14,799/5,107,435):
sufficient set 23% of roots / 30% of fact mass — a solid 3-4x
reduction, though less extreme than the subset ratio (the full kernel
has proportionally more fptr-reaching structure: 18.2% ancestor
classes vs 8.4%, and 36k function roots are 11% of all roots by
themselves). Function roots actually read at icall planes: 17,522 of
36,242 — half the function-root alphabet never appears in any fptr
plane. The sufficient set is computed against all-function-roots;
restricting to the 17.5k observed answer roots is not sound a priori
(which functions surface depends on the solve), but a two-phase
schedule (solve, restrict, certify) could exploit it.

~80-90% of fact volume is provably irrelevant to the answers at real
scale. Contrast the old derivation-slice negative: its STATIC
Steensgaard alias closure kept 58% of harfbuzz classes (and bought no
time) because it must over-approximate which joins could matter. The
exact set is 4-6x smaller — the gap is dynamic evidence.

### Design sketch: lazy origin introduction (demand-driven roots)

1. A := reverse-{a,f}* ancestors of all fptr classes (initial quotient).
   Mint function roots + origins whose class ∈ A. Drain.
2. Expand: mint any origin found in the plane of a POINTER that owns a
   cell in A (cellsOf is static; pointer planes are dynamic — origins
   are introduced by observed potential, not static alias closure).
   Seed new roots (monotone: addFact + continue draining — the cheap
   direction of incrementality, no wiring involved).
3. Merges coarsen the quotient -> recompute A (coalesced classes can
   join in-edges of one side to out-edges of the other, so A grows).
   Repeat 2-3 until A and the root set are stable; then resolve icalls
   as usual (outer wiring fixpoint composes with this inner loop).

Soundness sketch (FI): take the first missed join, in derivation
order, whose consequences reach an fptr plane. By minimality all
earlier flows/joins are present, so the witness origin o reaches the
join's pointer parent in the restricted solve too; that parent owns a
cell in A at the fixpoint (its consequence path exists in the final
quotient); so rule 2 minted o and the join fired — contradiction.
fs mode needs one extra coupling (VX bridges create connectivity, so
A-closure must add same-origin exact/X cluster coupling); FI has zero
bridges on every run to date.

Expected payoff at kernel scale if the subset ratios hold: fact mass
-> ~20% (planes, join sweeps, a-prop words all scale with it), memory
~12 GB -> ~3-4 GB, and the solve time dimension |roots| drops ~7x.
Validation gate as always: per-icall identity vs the full solve +
closure certificate restricted to minted roots.

## 2026-07-18: POPL'18 consistency check + novelty ledger

Read Chatterjee–Choudhary–Pavlogiannis, "Optimal Dyck Reachability"
(POPL'18) against our results: fully consistent, and it retroactively
explains two empirical findings — (1) our join layer independently
reinvented `BidirectedReach` (bidirected Dyck = equivalence, optimal
via union-find; our Lean fact-equivalence = their soundness/
completeness pair), and (2) their partition-vs-relation split is our
"OOM = closure size" diagnosis: the partition is O(m), enumerating
all pairs is the quadratic part — which is what flows-to avoids.
Their BMM-hardness for general Dyck (even constant treewidth)
justifies output-sensitivity (demand-driven roots) over hunting a
uniform algorithm, and their Lemma 3.4 potential argument says a
merge layer with delta-precise re-offers is the amortized-correct
form of ours — supporting that retry. Their Dyck-paren field model is
Java-only (cannot express container_of), which is exactly where our
Z_P shift encoding deviates.

Full classification — rediscovered (wave scheduling = Pereira–Pearce
wave propagation; a-SCC collapse = online cycle elimination; deltas =
semi-naive) vs defensible novelties (witness-exact unification inside
a directional solver; sound C fields as quotient-group weights at
scale; certificate-carrying runs; the measurement set; 1-bit VX
provenance) — recorded in docs/novelty-and-related-work.md, with the
pre-drafting diligence list (InterDyck/mutual refinement 2024–26,
Kelp/TFA kernel icall lineage, group-weighted Dyck instantiations).

## 2026-07-19: terminology correction + heap-identity directive (task #17)

CLARIFICATION (recorded so the paper doesn't overclaim): the solver is
ANSWER-ANCHORED (relation restricted to origin facts), NOT
demand-driven — all roots are minted and fully propagated. The
root-relevance measurement sizes the demand-driven opportunity (23%
of roots / 30% of fact mass at whole-kernel); the lazy-minting
mechanism is designed (§2026-07-18) but unimplemented. Subset ratios
UNDER-estimate relevance for the same reason coredump's sysctl pairs
need out-of-module VFS flow: cut boundaries sever data-flow.

Heap-identity conflation, micro-evidence (test/t_allocinit.c): a
wrapper that mallocs, stores a callback into the object, and hands it
out (return or out-param) is analyzed SOUNDLY by flows-to (both
icalls resolve; the saturation-path removeCallEdges/opaque treatment
does not fire in flows-to mode) but CONFLATED: one internal alloc
site = one object for every wrapper caller, so 2 callsites x 2
callbacks = 4 pairs instead of 2, at K=0 AND K=13 (field sensitivity
cannot split same-object smear). This is seq_open/devm_kzalloc in
miniature and scales with wrapper fan-in. Fix = task #17: selective
per-callsite cloning of wrapper constraint subgraphs (automatic
detection + yaml override, transitive with depth/size budgets, sound
shared-treatment fallback, loud). Expected: precision (fan-out tail)
AND time (closure law: splitting a shared identity shrinks
Sum|component|^2 quadratically).

## 2026-07-19: Lemma-3.4 merge discipline — NEGATIVE, does not transfer (task #18)

Tried the POPL'18-derived merge layer on the kernel subset (baseline
19.7B total / 12.4B join / 3.5B merge cycles). Four variants:
1. keeper by fact mass + joined-union-when-one-cluster + merge-time
   delta re-offer: 23.2B (+18%). Re-offers UNCHANGED (121M -> 123M):
   kernel cell lists span multiple clusters (container webs), so the
   exact-union case rarely fires and intersect still destroys marks;
   meanwhile the delta computation streams the heavy merged plane 3-4
   extra times per merge.
2. keeper by fact mass, no delta computation: 24.0B (+22%). The
   keeper policy itself is the regression: light-FACT hub classes
   with huge fan-out become losers, and the one-time pushes stream
   the merged planes along their edge lists.
3. keeper by edge-list size + eligibility scan: 22.1B (+12%) — the
   per-merge cell-list scan (find() per entry over veteran classes'
   thousands of cells) is itself ~1.5-2B.
4. keeper by edge-list size alone: 20.8B (+6%) — never better than
   rank.
REVERTED to union-by-rank + intersect (exact baseline restored,
19.6B). WHY the theory does not transfer: BidirectedReach merges are
payload-free (edge lists splice in O(1), nothing re-derives), so
small-to-large amortizes; our merges push merged fact planes along
the loser's moved edges and re-sweep merged cell lists — the cost
model the potential function assumes does not include either. Rank
already keeps veteran hubs implicitly. Mark preservation would need
per-side offer machinery (jdirty entries scoped to cell subsets),
whose bookkeeping exceeds the 6% the joined-filter currently saves.
Delta-precise merge re-offers are now CLOSED-NEGATIVE in both cost
regimes (pre- and post-wave-scheduling).

## 2026-07-19: BidirectedReach oracle (--cfl-bidi-prune) — roots pruned, mass untouched, kernel-shaped WIN (task #19)

Field-matched bidirected partition (union-find; colliding d / f<r>
labels unify targets; wildcard bases fold f labels; a-edges unify
endpoints) computed pre-solve in O(m·α): an origin whose partition's
forward d/f cone never meets an fptr partition cannot influence any
answer — its joins live inside the cone and every consequence stays
there — so its root is not minted. Sound per-iteration: the oracle
recomputes on the grown graph each outer iteration, so newly wired
callee edges re-admit origins whose cone grew.

Results (per-icall identical + closure certified everywhere):

| input         | prunable roots | oracle cost | fact mass | solve      |
|---------------|----------------|-------------|-----------|------------|
| libpng        | 13.5%          | 0 ms        | flat      | wash       |
| harfbuzz FI   | 35.2%          | 12 ms       | flat      | wash       |
| kernel subset | 38.3%          | 48 ms       | flat      | 7.7->5.4 s/iter (-30%) |
| whole kernel  | ~30% (95-110k) | ~2 s        | flat      | 497-553 -> 364-407 s/iter (-25%) |

Whole kernel (2026-07-19): resolution IDENTICAL (14,799 / 5,107,435)
across all 5 iterations — the cone argument holds at full scale. RSS
27.3 GB.

CAUGHT IN PASSING, needs its own diagnosis: the current-code
SEQUENTIAL whole-kernel baseline is 497-553 s/iter (root-relevance
run) vs 291/214-240 s/iter on the July-16 pre-refactor code — a ~1.7x
kernel-scale-only regression introduced somewhere in the parallel/
incremental refactor arc (harfbuzz and subset T=1 were verified at
parity, so it escaped the gates; pops are within 7%, so it is per-pop
cost, not scheduling). RSS is also up (27.3 GB vs ~12-19 GB era).
Candidates: FactSet width-guard branches on dense hot paths, the
fused-sweep restructure's cache behavior at 40KB planes, atomic
inWL/keyCount traffic. Action: SolverProf single-iteration
(--cfl-flows-to-max-iters=1) whole-kernel run against the old
profile, then bisect the refactor commits if needed.

TWO findings. (1) Static pruning cannot cut FACT MASS: the entangled
core is statically coupled to everything, so the prunable 35-38% of
roots carry ~0% of facts — the measured gap between the static oracle
(38%) and the exact irrelevance bound (77-86%) is exactly the part
only dynamic/lazy evidence can claim. The demand-driven mass win
still requires the lazy-minting loop. (2) The oracle still pays on
kernel-shaped inputs through a different channel: the ROOT UNIVERSE
shrinks 38%, so dense planes narrow proportionally (subset: 63k->39k
bits) — -30% solve on the subset where planes are dense-heavy;
harfbuzz (sparse-heavy) is a wash. Free at 48 ms, on by flag.

## 2026-07-19/20: kernel regression diagnosed and fixed — new production best (task #20, 9971899)

A/B with the July-16 binary (worktree at a7d9cff), single-iteration
whole-kernel, SolverProf both sides: work IDENTICAL (272M lookups,
275M offered facts, 123k+2.2k merges, same fixpoint), a-prop
IDENTICAL (185B cycles both), RSS IDENTICAL (27.2GB both — the old
"12.4GB" was a phase-of-run artifact; no memory regression ever
existed). The entire 239 -> 515 s delta was the JOIN phase: 358B ->
1072B cycles at equal volume. Cause: the 256-shard cluster registry
(introduced for the deferred-join parallel experiments, vestigial
since joins went sequential-only) — 272M redundant-confirm probes
chase hash-distributed shard headers spread over 16KB instead of one
flat_map header staying hot in L1, adding 1-2 dependent misses per
probe. Library-scale maps are small enough either way, which is why
the harfbuzz/subset T=1 parity gates missed it. De-sharded: 243 s
single-iteration = parity with July-16 (within 3%).

CAPSTONE (de-shard + --cfl-bidi-prune, full bclist): resolution
identical (14,799 icalls / 5,107,435 pairs, converged iter 4),
iterations 158.6/173.0/177.6/172.2/171.9 s = **14.2 min total solve**
(vs 19.6 min July-16 best, vs 41-46 min regressed+unpruned), wall
1:10:37 end-to-end, RSS 27.3GB. New production configuration:
sequential + --cfl-bidi-prune.

Meta-lesson for the falsified-hypothesis catalog: infrastructure left
behind by a rejected experiment is not free — the shards cost nothing
in the experiments' own gates and 2.1x at the scale the gates didn't
cover. Scale-dependent regressions need a whole-kernel timing gate
(single-iteration, ~4 min of solve) in the validation loop.

## 2026-07-20: IR-construct census (--ir-census) + the encoder gaps it found (task #13, ba5890d)

The encoder totality audit. Tool: enumerate every opcode/intrinsic/
external-callee/asm/constexpr kind in the corpus; classify against a
disposition table sourced from InstHandler (whose default handler is a
SILENT no-op — the exact failure mode the census exists to make loud).

Census findings:
- 0 UNDISPOSITIONED kinds on libpng / harfbuzz / whole kernel: the
  table is total over the real corpora.
- Kernel IR contains ZERO atomicrmw/cmpxchg/addrspacecast/landingpad —
  x86 kernel atomics are ALL inline asm (129,812 sites, 4,900 distinct
  strings): the asm ledger is the kernel's true atomics exposure.
- The external-callee ranking independently rediscovers static_call as
  the #1 boundary assumption (__SCT__might_resched 963 calls, ...).
- SUSPECT ptr-relevant instances were rare in IR form: kernel 18,
  harfbuzz 4, libpng 11 (landingpad/resume, C++ EH — ledgered).

Encoder fixes the census drove:
1. Four missing visitors: freeze, addrspacecast (copies), atomicrmw +
   cmpxchg on pointer slots (fused store+load).
2. THE REAL FIND — integer-laundered provenance dies at memory: clang
   lowers _Atomic function pointers to i64 atomics with ptrtoint
   constants and inttoptr reads; the load/store int-type guards
   dropped the whole idiom (test/t_atomicptr.c resolved 0/2 icalls).
   Register-side int provenance was already modeled (ptrtoint/binop
   visitors); the MEMORY hop was not. Fix: pointer-width int stores/
   loads emit deref edges under a bounded def/use provenance witness
   (ptrtoint upstream / inttoptr-or-store-onward downstream);
   interprocedural cases the witness declines are counted as explicit
   IntProvenance LEDGER lines — the census's no-silent-drop contract.

Impact: t_atomicptr 0/2 -> 2/2; libpng/harfbuzz answers unchanged;
KERNEL SUBSET RESOLUTION GREW 1045 -> 1049 icalls / 57,143 -> 58,132
pairs (+34% facts, +18% solve — the cost of edges that were missing).
First measured soundness recovery attributable to the census. Whole-
kernel post-census run in flight; its icall set becomes the new pinned
baseline. Remaining ledger entries (per run, machine-readable-ish):
inline asm data-flow (kernel), __SCT__ (task #14), landingpad/resume
(C++ EH), va_copy, interprocedural int provenance counts.

Whole-kernel post-census run (2026-07-20, de-shard + bidi-prune +
census fixes): **14,824 icalls / 5,135,527 pairs** (+25 icalls,
+28,092 pairs vs the pre-census 14,799/5,107,435 — recovered
long-laundered flows at full scale), converged iteration 4, solve
190/210/210/213/212 s = 17.6 min (the missing edges cost ~+20% over
the 14.2 min pre-fix best — soundness first), RSS 28.2 GB, wall
1:13:57. IntProvenance at kernel scale: 47,676 accesses modeled,
LEDGER 22,794 unmodeled interprocedural (explicit). These numbers are
the NEW pinned baseline; regenerate the sorted per-icall artifact
(--cfl-dump-icalls) on the next full run.

## 2026-07-20 (later): census remainder — strict gate, asm classification, ledger artifact (task #13 complete)

Three deliverables closing the census cycle (commit 0cf2783; full
study in docs/kernel-census/):

1. **`--ir-census-strict` (closed-world enforcement).** Aborts if any
   construct kind lacks a disposition; usable standalone or as a gate
   before a real analysis run (census tables suppressed, summary
   kept). Kernel passes with 0 undispositioned kinds — the "default
   visitor is a silent no-op" failure mode is now mechanically
   impossible to reintroduce unnoticed.
2. **Inline-asm classification by constraint signature.** The
   129,812-site "dominant untyped exposure" splits by what each
   template is PHYSICALLY able to do (outputs, indirect elementtype
   widths, reg-vs-immediate ptr args, memory clobbers): only
   **17,804 sites (13.7%) / 171 distinct templates are ptr-capable**;
   86.3% provably cannot move a pointer (narrow slots, immediate
   metadata symbols, pure barriers). Family analysis: bitops 7,336 /
   percpu %gs 5,918 / atomic RMW 1,310 / uaccess 1,149 / paravirt-ALT
   calls 293. Top modelable levers: percpu ptr slots (11 templates),
   asm ptr xchg/cmpxchg (~600 sites), ALT call templates (→ #14).
   Key refinement: imm-ptr (pointer bound to i/s/n/X constraint, no
   memory clobber) = link-time symbols in __bug_table/__jump_table —
   23,132 sites excluded from exposure honestly (with-clobber variant
   stays ptr-in-reg).
3. **`--ir-census-out=<json>` ledger artifact.** Full census as JSON:
   dispositions + counts, ALL extern callees, constexprs, the
   classified asm table, and a `ledger` array = the per-corpus
   unsoundness bill. Kernel artifact pinned at
   docs/kernel-census/linux-6.8.2-ir-census.json.gz.

Residual kernel ledger after classification: 171 ptr-capable asm
templates, 22,794 declined interprocedural int-provenance accesses,
1,136 extern decls (top mass __SCT__), 16 SUSPECT intrinsic instances.

## 2026-07-20 (later still): module-level census — linker-mediated pointer flows (task #22 phase A)

User-flagged gap: linker-introduced/setup pointers (kernel initcalls,
userspace ctors/PLT). Status check: llvm.global_ctors/dtors and ifunc
resolvers already handled (CallGraph.cc:5585/5606); PLT is sub-IR. The
kernel hole is real and DOUBLY invisible: x86-64 initcalls are
MODULE-LEVEL inline asm (PREL32 .section + .long fn-.), unseen by both
the instruction census and the edge builder (no getModuleInlineAsm
handler existed anywhere); consumption loads linker-defined
__start_/__stop_ externs (ExtGobjs) that flows-to resolves to ∅.

Census extended (module_level in the JSON artifact): module-asm blobs
by target section, sectioned globals with ptr-bearing counts, undefined
extern globals with linker-bounds flag + use counts, .discard.
addressable stub tally. Kernel: 1,494 modules with blobs / 27 sections
/ 3,490 sym entries (pci_fixup 1,671, tracepoints_ptrs 964, initcalls
646); 106 linker-bounds externs WITH real IR loads (__start___param 5,
__start_builtin_fw 6, ...); 16,915 addressable stubs naming 12,597
distinct functions = 21.8% of the corpus referenced via linker
plumbing. vmlinux content cross-ref (ABS64 vs PREL32 sampling of every
bounds pair in the linked image): fptr-relevant arrays = initcalls,
.init.setup (314), __param (534), pci_fixup, ftrace_events (1,828),
__bpf_raw_tp_map (964) ≈ 6,100 pointer entries; the multi-MB arrays
(orc, bug/ex/jump tables, mcount) are patch/unwind metadata — no
value flow. Phase B model: section-array unification (__start_X/
__stop_X extern ↔ synthetic node fed by section-X globals + module-asm
targets via addressable stubs); differential test = do_one_initcall
V-set ∅ → ~646 initstubs. Study: docs/kernel-census/README.md.

## 2026-07-22: section-array model shipped — linker flows closed, universal-extern lesson (task #22 phase B, 4907f3b)

The model: (1) module-asm-referenced functions are address-taken (the
linker embeds their address; 12,597 fns minted); (2) each undefined
__start_X/__stop_X extern with fully-enumerated contents gets its OWN
node identity (NodeFactory extGobjOverrides — closed world justifies
leaving the universal fallback); (3) dual wiring by member provenance:
section-attributed globals ARE the elements (value edges: bounds
aliases their objects), module-asm PREL32 targets are ENCODED (deref
edges, read out by the gated offset_to_ptr rule: inttoptr(add-chain
with ptrtoint p) pulls deref(p) IFF the chain loads through p itself);
(4) metadata/patching/module-linking families (static_call -> #14,
ksymtab, jump/ex/bug/orc/mcount) excluded + LEDGERed; unresolved-entry
sections keep universal + LEDGERed. Companion spec fix: binop visitor
now emits a-edges from EVERY pointer-derived operand (the old
"other operand must be constant" guard WARNed-and-dropped the
offset_to_ptr consumer shape; per-corpus cost: km +399 pairs).

Debugging lessons, measured:
- FIRST DESIGNS LEAKED +2.7M pairs (72% = 1,671 pci-quirk stubs at
  ~1,500 unrelated icalls; fuse_conn_put -> quirk). Value-side vs
  deref-side wiring produced BIT-IDENTICAL results — the tell that
  neither was the channel: getValueNodeFor returns the UNIVERSAL node
  for every ExtGobj, so all wiring landed in the unknown-memory hub
  that every unmodeled extern load reads. Own-identity override killed
  it: UNIQUE_ID pairs 1,935,100 -> 925 (exactly pci_do_fixups).
- Under own identity, ABS64 vs PREL32 need DIFFERENT encodings
  (in-place aliasing vs encoded deref) — universal conflation had
  masked the distinction (both "worked" in the micro test).
- km A/B: minting 12.6k roots alone = +26 pairs (free); wired flows
  +15.6k = real store chains (param->sysfs attrs, trace registration)
  spread by the KNOWN field-insensitive hub joins (#17/#21).

NEW PIN (test/baselines/kernel-full6-*): whole kernel 14,850 icalls /
5,866,561 pairs (+26 icalls, +731k pairs over pre-#22; superset
verified, 0 removed), converged iter 4, solve 19.9 min (238-242 s/it),
RSS 31.9 GB. do_one_initcall 85 -> 735 targets (649 initstubs) — the
flagship differential. Residual growth decomposition: initstubs 62k,
SCT 142k (real &tramp flows into __static_call_update void* params),
other 553k (trace/param members through registration stores + hub
spread) — the quantified motivation for #17/#21.

## 2026-07-23: soundness items closed — asm interface closure + static_call (tasks #23 + #14, 287f3c9/4aab066)

Inline asm (census top levers): handleInlineAsm extended with (a)
ptr-WIDTH indirect slots under the laundering witnesses (asm atomics
xchgq/cmpxchgq on i64 fptr slots; ptrtoint-CE inputs unwrapped — the
i64 CE otherwise lands on the shared ConstantInt node), (b) raw-ptr
register/address inputs: reads unconditional (this_cpu_read_stable),
writes/copies gated on declared memory effects; per-run InlineAsm
LEDGER. t_asmpercpu.c 1/3 -> 3/3 exact; km +41 icalls (bpf prog
invocation, tick broadcast, kprobes, user-return notifiers).

static_call: __SCT__X calls become icalls reading deref(__SCK__X).
TWO conflation battles, both param-sharing: (1) __static_call_update
modeled as a PRIMITIVE (per-callsite func -> deref(key)) — generic
wiring unioned every key through the shared param (cond_resched
"resolving" to alloc_insn_page); (2) tracepoint keys live in the hub,
so tp_func sites take the syntactic edge to __traceiter_X (probes
transitively covered by the iterator icall) + tracepoint_probe_
register wired per-callsite; dynamic-key updates suppressed+LEDGERed.
cond_resched = exactly {__cond_resched, klp_cond_resched,
__static_call_return0}.

NEW PIN (kernel-full7): **16,720 icalls / 5,644,481 pairs** — +1,870
resolved icalls with NET -222k pairs vs full6: the updater primitive
DRAINED 611k hub pairs (SCT trampolines + escaped funcs no longer
enter the hub through the shared param — most of the 142k SCT channel
from the #22 postmortem reversed), asm closure added 391k recovered
flows. Solve 20.1 min, RSS 40.1GB. Residual: 151k tp_func-tramp-as-
target pairs from tracepoint-struct hub residency (pre-existing,
quantified; #17/#21). Ladder green: micro exact, smoke 4/4, harfbuzz
zero-diff. LESSON (twice now): shared-parameter conflation through
tiny utility functions (sort, __static_call_update) is the single
biggest precision channel in the kernel — the strongest evidence yet
that #17-style selective cloning of a HANDFUL of functions buys
outsized precision.

## 2026-07-23: lazy minting shipped (task #21) — catch-up round required; A-loop sufficiency REFUTED

Implemented `--cfl-lazy-mint` (62b2786): A := backward reachability
from fptr classes over reversed {a, f} edges PLUS cell->owner hops
(the owner hop must apply to the WHOLE closure, not only fptr-feeding
cells, or witnesses of intermediate joins are missed); origins and
identity candidates outside A are deferred, and every drain fixpoint
recomputes A on the merge-coarsened quotient and mints new entrants
(the "observed potential" of the design sketch reduces to exactly
this closure on the live quotient, because fact propagation over a/f
edges IS graph reachability). Function roots always minted.

Sub-kernel validation: bit-identical everywhere (8 micro, libpng,
harfbuzz, km subset), fact mass 32-42% of eager, solve ~2x faster.

WHOLE KERNEL REFUTED THE SUFFICIENCY CONJECTURE (§2026-07-18's
first-missed-join induction): -5 icalls / -5,737 pairs, strictly
one-sided, all in ops-struct registrations consumed through circular
list_head walks (tcp_ulp subflow/espintcp/cls_cgroup, 9p transport,
decompressor callbacks). The A-loop stabilized (8 rounds) with the
needed witnesses still deferred: on a cycle, each node's join needs
the neighbor's merge for its consequence path to reach an fptr —
mutual witness dependence the demand-driven loop can never enter.
The induction's gap: a witness's OCCURRENCE path and another
witness's CONSEQUENCE path can each require the other's merge; small
shapes resolve through owner-hops (we could not build a <=7-node
counterexample against the A-loop — constructing one is open), the
kernel's circular lists do not.

FIX (1fa5186): catch-up round at convergence — mint every
still-deferred root, keep draining. Exact BY CONSTRUCTION via closure
confluence, machine-checked (proof/lean 7b9b028: `sderiv_catchup`
staging theorem, `catchup_answers_complete`, plus the necessity
counterexample `answer_not_derivable_restricted`; GAPS.md F11 records
the open sufficiency problem).

Whole-kernel scorecard (from-scratch driver mode, pinned in
test/baselines/kernel-lazy-*):
- answers: identical (16,720 icalls; dump pinned at 5,644,875 lines)
- fact mass: 921M final vs 1,913M eager = 48% — catch-up mints only
  the never-merged residue (21,168 roots), not the 125k deferred
  classes that merged into minted ones; end-state win SURVIVES
- roots: 141,271 vs 245,858
- restricted solve iterations: 120-139 s vs eager 224-246 s (2.0x)
- BUT catch-up drains cost 578 + 702 s (two, one per driver rebuild
  reaching convergence) -> total 36.4 min vs eager 20.1 min: the
  catch-up currently EATS the time win (task #24: single catch-up via
  incremental mode; diagnose why a 21k-root/48M-fact top-up drain
  costs 2.9x a full eager iteration — suspected joined/jdirty
  re-offer rescans on the warm state)
- peak RSS 40.0 GB = eager's 40.1: kernel peak is front-end loading,
  not the solver, in BOTH modes; solver-phase RSS observed 14.9 GB

BONUS BUG the identity gate caught: the SCT trampoline-self filter
compared Function* pointers, but __SCT__ symbols have no IR def, so
funcRootOf holds an arbitrary per-TU decl (pointer-ordered container
iteration — deterministic per binary, flapping ACROSS binaries).
full7-vs-lazy dumps differed by exactly 1 such line; km pin drift
81,286 -> 81,660 was 367 leaked self-pair copies. GUID-based filter
removes the class (km: -367, zero other changes; kernel: -1,794).
Deterministic subset counts from this commit: km 1,482/81,293,
harfbuzz 2,824. The kernel-full7-stats.txt subset numbers were stale
artifacts of this nondeterminism.

### 2026-07-23 addendum: #24 scoping — where lazy minting actually pays

Since kernel peak RSS is the front-end in both modes, kernel-FI alone
does not justify further lazy-mint optimization: even a proportional
catch-up (~1-2 min instead of 578+702 s) lands at ~12-17 min vs eager
20 — parity to modest. Scoping decision: #24 runs two cheap
experiments (incremental-mode single catch-up — noting #15's kernel
negatives may not transfer; profile the 2.9x-overpriced top-up drain,
suspect jdirty/joined re-offer rescans), then gates on the regimes
where the SOLVER is the peak: field-sensitive mode (the original
harfbuzz/K=13 closure blowup — lazy's 48-52% mass cut applies there)
and #17 cloning (demand-driven minting = clone only identities in A).
If the experiments disappoint: lazy-mint stays non-default for kernel
FI, kept as the fs/#17 enabler, negative result documented. Separate
levers noted: front-end peak reduction (per-module edge extraction,
release IR) would make solver mass the true peak — turning lazy's
fact-mass cut into a peak-RSS cut; F11 (provable sufficient root set)
removes the catch-up and keeps the 2.06x solve win.

## 2026-07-23: conflation report v1 (--cfl-conflation-report) — the summary/clone input queue

New post-solve measurement ranking FUNCTIONS as summary/clone
candidates: (1) shared-formal conflation grouped by CLASS (callers x
facts resident in a pointer-formal's merged class = what a
per-callsite summary would de-mix); (2) allocation-site identity
spread (classes carrying an internal alloc root, attributed to the
wrapper + its caller count). Runs in ~3 s at km scale.

km subset verdict (deterministic binary, eager):
- ONE mega-class c513 holds the hottest formal/ret of 5,698 of the
  6,184 called+defined functions (92%), callerWeight 90,709, 34,051
  facts — the type-erased void*/callback-data channel (kthread fns,
  trace callbacks, workqueue/timer payloads). Every other top class
  carries the SAME 34,051-fact plane: the hub's fact set saturates
  the entire hot region. Splitting c513 is not one lever among many
  at km scale — it is the only lever visible above the noise floor.
- AllocSpread confirms the dup family as the secondary, immediately
  actionable tier: kstrdup(35 callers), bpf_map_area_alloc(23),
  kmemdup_nul, kstrndup, shmem_alloc_inode(30) — every top alloc
  root's spread saturates at ~2,100 classes = hub satellites.
Next: decompose c513 membership (which tiny utilities' formals
bridged 5.7k functions into one class — TopMerge/absorbed-member
samples name them) -> those utilities are the first summary/clone
targets; rerun the report at whole-kernel scale alongside the next
pinned run.

### c513 gluer decomposition (km, 2026-07-23)

HubMembers: c513 = 28,397 merged dense classes / 203,246 values —
11,184 formals, 146,730 instructions, 45,327 assistant nodes, only 4
globals (console_sem, alarm_bases, kmod_concurrent_max,
cpuhp_hp_states). 8,669 functions contribute members. Top
contributors by member count: ___bpf_prog_run (1,265 — the BPF
interpreter's untyped register file is a structural blender:
everything reaching BPF unifies through it), ___slab_alloc /
pcpu_get_vm_areas (allocator internals — the classic freelist
channel: free-pointer writes INTO object memory chain every slab
object of every cache into one memory web), __lock_acquire (lockdep
generic key/pointer stores), page-table walkers
(handle_mm_fault/copy_page_range — int-provenance pte words),
build_sched_domains/load_balance (per-cpu scheduler webs).

CAVEAT: member count measures hub RESIDENCY, not causality — big
functions rank high just by instruction count. Causal confirmation =
ablation probes (measurement-only body-edge exclusion per suspect,
rerun km ~5 min, measure c513 size): the ranked suspects are
 1. slab/percpu allocator internals (freelist channel — known
    points-to killer; candidate treatment: allocator-internals
    summary, i.e. object memory is opaque to the allocator's own
    bookkeeping accesses),
 2. ___bpf_prog_run (interpreter — candidate: model BPF program
    invocation at the bpf_prog level, exclude the interpreter body),
 3. __lock_acquire/lockdep (debug machinery, likely excludable),
 4. pte walkers (int-provenance interplay).

### c513 CAUSAL attribution — merge-witness provenance (km, 2026-07-23)

Residency was a red herring: ablating the top residents
(___bpf_prog_run, ___slab_alloc+__slab_free, __lock_acquire) each
moved c513 by <0.5% — three null results. HubMerge (join-witness
provenance, needs --cfl-root-relevance) gives causality: 28,396 of
the run's 29,583 joins (96%) landed in c513, 10,187 distinct
witnesses, 0 from a-SCC collapse. Top witnesses:

  x13946  .str.5            <- ONE anonymous string literal = 47% of
                               ALL joins in the program
  x508    <synthetic c517>
  x285/270/262  __bpf_trace_tp_map_task_newtask / __tracepoint_ /
                __tpstrtab_task_newtask   (tracepoint static trio)
  x227    kmalloc_trace     \
  x143    __kmalloc          |  internal heap objects of the BASE
  x57     kmem_cache_alloc   |  allocators' own bodies
  x41     __alloc_percpu    /
  x45     .str.1            (more rodata strings)

TWO causal mechanisms, each with a principled treatment:

1. RODATA WITNESSES (strings, __tpstrtab, const tables): shared
   literals sit in thousands of `const char *name` pointers; under
   FI cells a join keyed by a shared literal merges whole-object
   memory of unrelated structs. Treatment sketch: a rodata object's
   home cell is IMMUTABLE (no runtime stores into rodata), so reader
   cells can COPY from the home cell (directional a-edge) instead of
   UNIFYING with it — read flows (const ops tables -> icalls) are
   preserved, reader<->reader unification disappears. Grammar-level
   refinement: needs the no-rodata-stores assumption stated, a
   solve-time LEDGER for stores whose base carries a rodata origin
   (violation counter), and a Lean look (mal restricted to writable
   witnesses). Expected: kills ~half of km joins outright.

2. BASE-ALLOCATOR INTERNAL IDENTITY (#17 confirmed causally): the
   internal object of __kmalloc's own body flows to every caller and
   keys cross-caller joins — t_allocinit at the root of the heap.
   Treatment: FRESH summary for base allocators with definitions
   (suppress the internal identity, per-callsite AllocSites already
   exist) — the summary pipeline's first confirmed entry, cheap.

Order: (2) first — small, sound, immediately confirmable; then (1)
as the big lever, in tandem with per-field cells (fs mode shrinks
what a merge conflates even before the rodata refinement).

## 2026-07-24: transfer summaries shipped (task #26) — isAllocFn retired, two defects fixed

--func-summaries=func_summaries.txt: callsite-applied atom summaries
(FRESH/CPY/ALIAS/ST/LD/NONE; ordered, first-match-wins, prefix
support), AUTHORITATIVE over the legacy hardcoded isAllocFn table
when loaded (without the flag, legacy path bit-identical). A summary
at a callsite is a zero-cost infinite clone — per-callsite identity,
no shared formal/ret mixing. Seeded with the full isAllocFn migration
+ the dup family with CPY.

Two measured defects fixed:
1. LIVE SOUNDNESS HOLE: kmemdup was in isAllocFn, allocator bodies
   are skipped, so every dup's memcpy was DROPPED — kmemdup'd ops
   never resolved (t_kmemdup.c: 0/2 legacy). CPY(ret<-arg0) restores
   the copy as a shift-preserving cell edge: 2/2 EXACT.
2. ALLOCATOR-RET WITNESS BRIDGE (the km ~470-join channel): the
   alloc branch wired the allocator's shared return-node class to
   every callsite; that class's identity root keyed joins bridging
   ALL callers' objects. Suppressed for summarized allocators.
   t_allocinit: 4/2 conflated -> 2/2 EXACT — the baseline conflation
   micro test's smear was THIS bridge, not the wrapper-internal
   site; no cloning needed. Task #17's cloning scope shrinks to
   genuinely non-summarizable wrappers.

km eval (vs 81,293 pin): 80,531 pairs = -763 conflation removals
(tracing_stat_open seq-ops smear 375, shmem/bpf fs_context ops
cross-contamination, swap bio callbacks — all ret-bridge shapes),
+1 dup recovery (__cgroup_bpf_run_filter_sysctl ->
proc_doulongvec_minmax: the kmemdup'd sysctl-table class; kernel
scale will surface many more from drivers/fs). 433 functions
summarized, 70 CPY edges. harfbuzz identical; libpng identical;
micro suite identical except the two intended fixes; smoke 4/4.
Hub c513 persists as expected (string glue = #25's job).

Whole-kernel run with summaries = next pinned baseline (answers
change: +dup flows, -ret-bridge conflation); rides after the
in-flight kernel conflation-report run.

### Whole-kernel conflation report (2026-07-24, eager, 2:02 wall)

Same structure as km, bigger: hub c5500 holds the hottest formal/ret
of 44,259 of ~57k functions (78%), 164,473 merged classes / 1.2M
values; 161,002 of 168,779 witnessed joins (95%) land in it (3,483
from a-SCC collapse). RootRel at current features: sufficient set
37.96% of roots / 34.5% of fact mass. Top witnesses:

  x92798  guc_wq_item_append::load   <- ONE i915 GuC ring-buffer load
          identity = 55% of ALL kernel merges. A !hasIn load-result
          identity (unmodeled io/ring memory) spreading through the
          type-erased drm/i915 request web.
  x2161   __tpstrtab_initcall_level  (rodata string tier, as at km:
          .str.1/.str.45 among the hub's 9 global members)
  x784    __per_cpu_offset           (percpu base array)
  x690/663/532  initcall tracepoint statics/allocas
  x438/299/59   kmalloc_trace/__kmalloc/kmem_cache_alloc rets
          (drop with --func-summaries)

CAVEAT (applies to km .str.5 too): witness counts conflate SEEDING
the hub with RIDING it — an early-merged witness keys joins the
grown hub makes downstream. Causal probe before designing #25:
targeted no-mint ablation of the top witnesses (measurement-only
flag), km-fast then kernel. The GuC load may also be its own bug
class (identity minted for loads from unmodeled device/ring memory —
compare universal-ptr handling).

### Witness over-determination (2026-07-24) — single-witness ablation is the wrong knife

Probes added: HubWitness (member anatomy of top witness classes) and
--cfl-ablate-mints (MEASUREMENT-ONLY no-mint by global name /
containing function). Results:
- intel_guc_submission.o analyzed ALONE (single-module runs work;
  extern boundary goes universal): guc_wq_item_append::load keys just
  7 local joins, class = 3 folded loads + assistant nodes, ablation
  changes nothing. Its kernel-scale x92798 is therefore mostly
  cross-module class content + hub-riding — kernel HubWitness anatomy
  rides the next kernel report run.
- km .str.5 no-mint ablation: NULL. Hub 28,323 vs 28,385 joins,
  answers IDENTICAL. The 13,946 count was ~99.6% ride-along.
- Even the allocator-ret channel: summaries suppressed it and the km
  hub moved 28,396 -> 28,385, yet answers improved by -763 pairs.

LESSONS: (1) joins are massively over-determined — the hub is glued
by a witness ENSEMBLE (10k+ at km), so removing individuals moves
nothing; the mergeWitness histogram records first-firer, not
necessity. (2) Answer precision and closure size are different
currencies: summaries bought answers by cutting FLOW conduits
without shrinking the hub. (3) #25 must change the JOIN RULE for a
whole witness class (rodata copy-not-unify), not remove witnesses;
its win cannot be read off the histogram. Cheap upper-bound
estimator before building it: a probe that skips joins keyed by
isConstant()-global origins entirely (over-removes: also breaks
const-table home-cell reads, so answers drop; gives upper bound on
hub reduction).

### Whole-kernel pin with transfer summaries (2026-07-24, task #26 closed)

New pinned baseline test/baselines/kernel-summ-*: 16,532 icalls /
5,646,829 pairs, wall 3:02, solve ~250 s/iter (summaries cost
nothing), 2,248 functions summarized / 383 CPY edges. vs the lazy
pin: +5,802 dup-flow recoveries (per-netns kmemdup'd fib rule ops =
919 pairs at call_fib_notifier alone, MSI descriptor ops,
decompressor/driver contexts, sysctl tables — all previously DROPPED
by the isAllocFn body-skip hole), -1,659 ret-bridge smear removals
(sysfs attribute cross-kobject, drm_flip_work, ACPI SCI lists,
crypto ctx), -188 icalls that only ever resolved to smear. Reviewed
both directions; no genuine flow lost.

### Rodata-join estimator probe (km, 2026-07-24) — #25 upper bound: ~16%, not the lever

--cfl-probe-rodata-joins (skip ALL joins keyed by rodata-bearing
witness classes; measurement-only over-removal): 9.17M join offers
skipped; merges 24,974 vs 29,592 (-15.6%); hub facts 28,344 vs
34,045 (-17%); total facts 58.2M (-19%); answers -20,198 (25% of km,
all removals — const ops-table reads ride the skipped joins; the
real copy-not-unify would preserve those, keeping answers while
capping the closure win at the numbers above).

VERDICT: the copy-not-unify refinement is bounded at ~16% closure
reduction (km) — real but NOT the fs-mode savior the witness
histogram suggested. Over-determination again: writable-object
witnesses co-key most rodata-keyed merges. The hub is an ensemble
property. Disposition: #25 downgraded to a modest-win refinement,
NOT the next big build. The closure-size lever hierarchy is now:
per-field cells (field sensitivity shrinks what every join
conflates — the original plan) + identity splitting (#17 confirmer
sweep + cloning), jointly; single witness-class rules cannot split
an ensemble-glued hub. Three probes, three falsified sizing
hypotheses — the measurement stack is earning its keep.

## 2026-07-24: per-field-cells workstream reopened — fs status corrected

Re-measured hb fs13 with the current stack (summaries, bidi, all
task #14-#26 machinery): 40 s wall (was 33 min on 2026-07-08 —
bidi-prune mints 7,834 vs 12,233 roots, plus the accumulated solver
work), 673M native facts, 259 VX bridges. TWO STALE NARRATIVES
CORRECTED:
1. The would_match_input fs soundness bug is GONE — all 7 match
   functions resolve, identical to FI, and today's dump is
   byte-identical to the July-17 hb-fs13 pinned baseline.
2. That baseline was ALREADY identical to FI: fs13 has bought ZERO
   precision on harfbuzz since mid-July. The July-8 "29 pruned (25
   source-verified correct)" state was transient; whatever fix landed
   in the Jul 8-17 window (incremental solving / bridge rework era)
   both cured the soundness drops and re-admitted the 25 infeasible
   pairs. Not summaries (fs13 without --func-summaries: same 2,824).

The per-field-cells problem statement is therefore NOT "fix the fs
bug" but RECOVER DISCRIMINATION: find which shift-plane flow admits
the 25 known-infeasible pairs (names + source evidence in the
2026-07-08 LLM-audit section). Entry point: trace one audited pair
(hb_ucd_script -> would_match_input's match slot) via
--cfl-trace-func/--cfl-trace-fptr; if it arrives via the X plane,
the wildcard chain on the path names the smear source. hb fs13 at
40 s makes this a fast-iteration debug loop. Kernel-side fs cost:
km fs13 measurement in flight.

### fs discrimination loss DIAGNOSED (task #27, 2026-07-24) — it is the hub, and it is one problem

Trace (--cfl-trace-func=hb_ucd_script --cfl-trace-fptr=
would_match_input, fs13): the root reaches the fptr class c8813 via
BRIDGE-INIT as bridged facts at ALL shifts, from an already-smeared
partner class. c8813 is the fptr class of 270 icalls (paint funcs,
shape features, match slots — one merged class); its cluster keys
include .str.18 (string literal, shift 0) and the
hb_accelerate_subtables apply-array origins (variable-index GEP →
fx wildcard). Rodata-probe control: skipping all rodata-keyed joins
drops hb fs13 to 1,876 pairs but ALL 30 would_match_input targets
survive — the mega-cluster re-forms through its other keys.

CONCLUSIONS:
1. fs discrimination died because the fptr CLASSES merged — shift
   planes cannot discriminate what unification has already conflated.
   Not a solver bug: every join is grammar-licensed; the Jul 8-17
   convergence with FI was the closure getting more complete, not
   less sound.
2. The hb fptr mega-cluster is ensemble-glued (strings + variable-
   index fptr arrays + memcpy'd func tables), same over-determination
   as the km/kernel hubs. fs discrimination, closure size, and answer
   conflation are ONE problem: witness-keyed cell unification is
   inherently hub-forming on real code, and union-find transitivity
   across keys makes the ensemble effect unavoidable within this
   solver shape (phase-2 already proved the grammar licenses the
   equivalent smear via load/store laundering).
3. The discrimination lever is therefore IDENTITY SPLITTING (#17):
   fewer co-occurring witnesses = fewer cross-keys = smaller
   clusters. Per-field cells remain necessary (same-shift keying) but
   are not sufficient; they pay off only after identities split.
   Roadmap: #17 confirmer sweep + cloning FIRST, fs re-evaluated
   after, #25 stays downgraded (its keys are over-determined for
   discrimination too — measured twice now).

## 2026-07-24: confirmer sweep step A shipped (--cfl-confirm-fresh, task #17)

Body-confirms PURE-FRESH wrappers (returns trace only to fresh
sources through phi/select/cast; no escapes; no pointer side
effects — the strict criteria make the allocator body-skip sound)
and promotes them to allocator status, to fixpoint over wrapper
chains. t_freshwrap.c: 4 cross-smeared pairs -> 2/2 exact. Micro
suite unchanged; hb 45 promoted, answers unchanged (its cluster is
array/memcpy-glued, per diagnosis); km 19 promoted, answers/hub
unchanged.

MEASURED SIZING for step B (cloning): km rejections = 1,742
ret-not-fresh (mostly genuine: pool/cache returns, interior
pointers, wrapper-of-failed-wrapper cascades), 140 ESCAPES (fresh
pointer stored/passed = the alloc-init wrapper class, t_allocinit
shape at scale — THE cloning queue), 16 ptr-side-effects. Step B =
per-callsite cloning of the escape class with depth/size budgets;
the 140-function km queue (kernel-scale count TBD on next full run)
is small enough for exhaustive cloning.

### km fs13 cost (partial, 2026-07-24): first drain 2,261 s vs FI ~10 s

km fs13 (summaries config) killed after iteration-1 drain: 37.7 min
for one drain at km subset scale (~200x FI), 4,852 wildcard nodes
(ptrtoint-escape 3,467, union-initializer 1,777 dominant). Kernel
fs13 at this cost = days per run. Confirms the post-#27 ordering
twice over: fs currently buys zero discrimination AND is unaffordable
before identity splitting shrinks the clusters; re-evaluate fs after
#17 step B.

### Step B v1: alloc-init auto-summaries (2026-07-24) — mechanism proven, kernel shape mismatch

The confirmer now classifies stores into the fresh object graph:
non-pointer/null stores are tolerated, stores of FORMAL pointers
generate {FRESH, ST(*ret <- argI)} summaries (per-callsite infinite
clone, no graph duplication — the ST atom applicator already
existed). t_freshwrap extended with an alloc-init wrapper x2
callers: 16 smeared pairs -> 4/4 EXACT. Micro suite/hb unchanged.

km: 23 promoted (+4 from non-ptr-store tolerance), but ZERO
alloc-init conversions — the kernel's 130 remaining escape-class
wrappers do not fit the direct store-formal shape (out-params,
registration calls, values derived through phis/calls). Next
decision needs their anatomy: sample the escape rejections (add
name+reason dump), then choose richer shapes (FRESH(argJ*)
out-param atom, @global ST sources) vs true budgeted cloning.
Identity-splitting scoreboard so far: summaries drained answer-level
conflation (-763 km, -1,659 kernel) but the ensemble hub needs the
escape class converted before fs re-evaluation makes sense.

### Step B v2: init-helper composition (2026-07-24) — proven on micro; kernel needs two extensions

The confirmer now composes ONE level of init helpers: a helper is
INIT-ONLY in param j (param used solely as store base; stored values
= own formals / non-ptr / null / self-linkage; no other ptr side
effects; void return), and the wrapper maps the helper's stores
through the callsite into its own ST atoms. t_freshwrap extended
with the vm_area_alloc/vma_init shape: 6/6 EXACT (was cross-smeared).
Micro suite unchanged. One walk bug found en route: a formal stored
into a SIBLING param's memory is init, not an escape of the formal.

km: still 0 compositions — real kernel init helpers (vma_init,
desc_set_defaults) fail on exactly two missing capabilities:
 1. stores of GLOBALS into the object (vma->vm_ops =
    &vma_dummy_vm_ops — the fptr-relevant init!): needs a
    ST(*ret <- @global) atom variant (SummaryAtom gains an optional
    GlobalValue* source; applySummaryAtoms edge from the global's
    value node).
 2. NESTED init helpers (vma_init calls vma_numab_state_init(vma)):
    needs InitInfo composition to fixpoint (helper valid if its
    callees on the obj param are themselves init-only — same
    recursion the wrapper level already does once).
Both mechanical; the call-escape bucket (80 of 130 at km) is the
prize. After those: whole-kernel eval + re-pin, then fs re-check.

### Step B v3 tolerances (2026-07-24): funnel converging, kernel wrappers stack features

Added: ST(*ret <- @global) atoms (ops-table init — applicator +
walk + helper + composition), recursive InitInfo (nested init
helpers, cycle-safe via in-flight cache default), wrapper-level
self-linkage stores (INIT_LIST_HEAD), free-family call tolerance
(error-path kfree). t_freshwrap still 6/6; micro suite/km answers
unchanged.

km funnel state: escapes still 130 / 0 conversions, but buckets
migrate as tolerances land: call-escape 80->50, store-other 22->6;
now other-use 24 (sample suggests refcount/atomic ops on object
fields), init-from-call 12 (SUB-ALLOCATIONS: vm_area_alloc stores a
second kmem_cache_alloc result into the object — needs a FreshSub
atom: per-callsite opaque sub-object stored into *ret; NodeFactory
needs a keyed multi-object-per-callsite API), init-other 12.
READING: real kernel alloc wrappers stack 3-5 features each; the
funnel converges only when the LAST feature of each wrapper is
tolerated. Next features by measured size: FreshSub (12+), other-use
anatomy (24), then re-measure. vm_area_alloc is the canonical
all-features test case (extract pinned at /tmp/vaa.ll shape:
formal store + global store + volatile self-linkage + sub-alloc +
error-path free).

### Step B v4: FreshSub atom (2026-07-24) — FIRST kernel conversions

FreshSub = a fresh anonymous sub-object stored into *ret
(vm_area_alloc's vma_lock shape): per-callsite anonymous value+object
pair (createValueNode(NULL)/createOpaqueObjectNode(NULL) are
multi-call-safe — no NodeFactory change needed), AllocSites identity
for minting, sub-result tolerated when its other uses are null checks
and error-path frees; isFreeFn also exempted in R3. km: 27 promoted,
4 ALLOC-INIT CONVERSIONS (the funnel's first), 34 FRESHSUB edges,
escapes 130->120; answers stable; t_freshwrap 6/6.

Remaining funnel: call-escape 50 (non-init/non-free callees —
sample next), other-use 24 (suspect refcount atomics), init-other
12, store-other 6. Incremental-mode note: FreshSub AllocSites
created during resolution-time application are not pushed to
newAllocNodes (from-scratch default unaffected; wire before enabling
incremental+confirm-fresh together).

### Step B asymptote (2026-07-24) — funnel converged at km; wrapper identity is NOT the km hub driver

Callee sampling showed a long tail (top x8 __raw_spin_lock_init);
added noop-intrinsic + curated benign-init tolerances (lock/waitqueue
/completion initializers — no fptrs at init time). Three tolerance
rounds: escapes 130->120->118, conversions PLATEAUED at 27 promoted
/ 4 alloc-init. The residue is multi-feature complex bodies
(mempool_init_node, rb_allocate_cpu_buffer) — summary composition
has captured what it cleanly can.

BIGGER FINDING: all 27 conversions produced ZERO km answer/hub
change. Combined with the summaries arc (whose ret-bridge fix
already drained the answer-level allocator conflation), the km
evidence says ALLOCATION-WRAPPER IDENTITY IS NOT THE km HUB'S
DRIVER — a partial falsification of the #27 'identity splitting is
the lever' reading: the ensemble glue is dominated by non-heap
witnesses (formal/no-in identities, arrays, strings). Open paths,
in decreasing expected value:
 1. whole-kernel eval of --cfl-confirm-fresh (drivers/fs have far
    more wrapper layering than the km core — the real test, rides
    the next pinned run);
 2. budgeted body CLONING for the 118-residue (different mechanism;
    only worth building if (1) shows wrapper conflation at scale);
 3. accept that hub splitting requires attacking formal/no-in
    identity webs (the 44k-member kernel hub's formals) — context
    sensitivity beyond heap cloning, the expensive frontier.
The confirmer machinery (5 shapes, atoms, funnel telemetry) stands
regardless: sound, validated, and the whole-kernel run decides.

## 2026-07-25: whole-kernel confirm-fresh verdict — falsification COMPLETE, ordering inverted

Kernel decision run (--cfl-confirm-fresh + pinned-summ config,
3:08 wall / 40 GB): 125 wrappers promoted (16 alloc-init), 2,366 ST
+ 457 FRESHSUB atom applications, escape funnel 656 (call-escape
294, other-use 106, init-other 62, store-into-loaded 40,
init-from-call 34, outparam 28). So conversions DO scale with the
corpus — and the answers got WORSE: vs the kernel-summ pin,
+11,088 pairs / -59, fact mass 1.91B -> 2.57B, hub joins 161k ->
165k. The +11k is ONE ops family (ring-buffer page iterators
direct_/cache_first/next/finish_page) smeared across hub icalls
(handle_edge_irq, percpu_ref_put, css_put): a converted wrapper's
per-callsite object is hub-RESIDENT — its callers' pointers live in
the mega-class, so every fresh object they touch joins the hub and
its contents reach every hub reader. Per-callsite identity
MULTIPLIED hub content instead of splitting it.

VERDICT (task #17 decision): allocation-wrapper identity splitting
does not improve — and at kernel scale actively worsens — precision
while the type-erasure hub stands. The causal ordering is the
INVERSE of the naive one: the formal-identity hub (44k functions'
void*/callback channels, 92-96% of all joins) must be attacked
FIRST; heap-identity work only pays afterward. Nobody in the
literature reports this ordering because nobody measures the middle
layer (code idiom -> graph structure -> bottleneck); 'context
sensitivity/heap cloning improves precision' is unconditionally
assumed. PAPER MATERIAL: the full funnel telemetry, the km-null,
and the kernel-regression triptych.

Disposition: --cfl-confirm-fresh stays OFF in pinned configs (kept
as validated machinery + measurement instrument); kernel-summ pin
UNCHANGED; frontier = the formal-identity channel (kthread/work/
timer void* payloads and equivalent), which is context sensitivity
on FORMALS, not heap cloning.

### Task #28 design core (2026-07-25): pair roots — C interface polymorphism as correlation

The kernel's interface lowering (user framing: how C realizes
polymorphism) has three shapes sharing one lost invariant:
(1) explicit (fn, data) registration pairs — kthread, request_irq
(handler, dev_id), notifiers, RCU, tasklets; (2) container_of self
— the callback receives &outer->member and recovers the receiver
geometrically (work_struct, timer_list); (3) ops + instance state
(f_op + private_data, netdev_ops + netdev_priv). Java object
sensitivity gets the correlation free (this IS the pair); C lowers
the receiver away, and pooling dispatcher formals destroys it —
producing BOTH measured pathologies at once: fn x data cross
products (precision) and the pooled channel itself (the 44k-formal
hub). Closest related work: JS correlation tracking (Sridharan
ECOOP'12); nothing for kernel C callback pairs.

Mechanism: PAIR ROOTS. Mint one root per recognized registration
site for the (fn, data) tuple; the pair fact travels containers as
one bit; at the dispatcher icall, resolution wires PER PAIR (callee
fn_r's formal bound to data_r, never the pool). Registration-site
correlation without body cloning, cost ~ registration sites, sound
degradation to the pooled channel + LEDGER for unrecognized flows.
Family (2) needs no pairs at all: fn read from origin o + argument
o+shift = same-origin binding at wiring — latent in the existing
fact/shift machinery. Family (3) = same-origin at the container.
Evaluation order: measure recognizable registration sites (census
of the ~10 dispatcher idioms), then a pair-root prototype on the
kthread channel (the c513/c5500 core), km ladder, kernel.

### Pair-root census, family 1 (km subset, 2026-07-25)

Explicit (fn,data) registration API callsites over the 338 km
modules: call_rcu 88, hrtimer_init 22, init_timer_key 21,
kthread_create_on_node 17, notifier-chain register 17, smpboot 4,
request_threaded_irq 3 — 177 sites total. The profile pair roots
wants: tiny, mechanically recognizable populations feeding huge
pooled channels (17 kthread registrations -> the ~398-caller c513
dispatch formal = the decorrelation ratio directly). Family 2/3
(INIT_WORK-style stores into work_struct/timer/ops containers) is
the larger population and needs an IR store-side census — next,
alongside the kthread pair-root prototype (step b).

### INVOKE: pair correlation as a transfer summary (2026-07-25)

Step (b) shipped not as a bespoke pair-root mechanism but as a new
atom in the transfer-summary vocabulary (commit cead1e8):
`INVOKE(argF:fK<-argD)` — "the fn at argF will be invoked with argD
bound to its formal K". Creatable by hand/census/proposer, imported
from func_summaries.txt, applied at callsites like every other atom.
Semantics at a summarized registration callsite:

- constant fn operand: assignment edge data -> fn's formal K
  (per-pair binding, no pooled mixing) + the invocation edge
  RE-ATTRIBUTED to the registration callsite (Callees insert;
  precedent: tp_func->__traceiter). No actual->formal edges feed the
  registration body, so the pooled dispatcher container drains
  naturally wherever all feeders are summarized.
- NULL fn: skipped (never invoked).
- non-constant fn: per-callsite fallback to the pooled arg/ret
  wiring (applySummaryAtoms returns needPooled; LEDGERed as
  "dynamic-fn pooled fallbacks") — sound degradation, measured.

Micro t_pairs.c is the decorrelation in miniature: reg() stores
(fn,data) into a table, dispatch() icalls fn(data). Baseline: 6
pairs — dispatcher {cb1,cb2} plus BOTH inner icalls cross-smeared
to {f1,f2}. With `reg INVOKE(arg0:f0<-arg1)`: 2/2 exact (cb1->f1,
cb2->f2), dispatcher channel drained (invocations live at the
registration sites). Regression ladder green: t_kmemdup 2/2,
t_allocinit 2/2, libpng smoke 4/4.

Kernel seeds (signatures verified against 6.8.2 source):
kthread_create_on_node (+FRESH for the ret task_struct — assumption
recorded in the file), init_timer_key (data = the timer itself; the
callback's container_of correlation rides the same binding),
call_rcu/_hurry/_tasks/_tasks_trace/_tasks_rude, call_srcu,
request_threaded_irq (dev_id -> formal 1 of both handler and
thread_fn). NOT seedable as INVOKE v1: notifier chains (fn behind
nb->notifier_call — needs field indirection), hrtimer_init and
smpboot (fn not a parameter — family 2/3 store-side territory).

km A/B vs the km-summ baseline (80,531 pairs) running; the
hypothesis under test: the kthread/timer/rcu pooled channels crack
(c17037-class callerWeight drops, rescuer_thread-style members
leave the hub) and per-registration data precision appears in the
answer diff.

Ops note from the km A/B launch (2026-07-25): km/kernel flows-to
runs REQUIRE `--cfl-compositional=false`. The first km INVOKE run
omitted it, fell into per-TU compositional mode, and died at the
boundary-cache sanity check with 6 missing `glob:` symbols — all
linker bounds externs (__start_rodata, __stop___param,
__stop___tracepoints_ptrs, ...). That is a PRE-EXISTING, documented
gap, not a regression: wireLinkerSectionArrays runs once after the
last module, so its cross-module edges fall outside every per-TU
graph and no TU exports the bounds symbols the compose-time
expected-set demands (the code comment at the call site says
exactly this). Verified by bisect: 66cf326 (the km-summ pin commit)
fails identically in compositional mode on the same input. The
strict sanity check caught the mode mismatch loudly instead of
composing over missing linker-array flows — working as designed.

### km A/B: INVOKE pair summaries drain the kthread/irq/timer/rcu pools (2026-07-25)

Config = km-summ baseline + the 8 INVOKE seed specs (10 atoms).
LEDGER: 135 INVOKE bindings applied, 348 dynamic-fn pooled fallbacks
(sound), 0 refs skipped.

Answers: 80,531 -> 70,876 pairs (-9,655, -12.0%); removed and added
sets reviewed both directions:
- REMOVED = precisely the pooled dispatch smear. Every kthread
  threadfn (worker_thread, rescuer_thread, kswapd, kcompactd,
  irq_thread, watchdog, oom_reaper, ...) lost its ~395-site fan-in;
  caller side is the irq/timer pools (handle_edge_irq 216,
  clocksource_watchdog 190, handle_fasteoi_irq 168, free_irq 144,
  __setup_irq 109, ...).
- ADDED = 2 pairs, both sound re-attribution accounting:
  __wait_rcu_gp/synchronize_rcu_tasks_generic icalls resolve to the
  summarized call_rcu family, whose constant fn operand THERE is
  wakeme_after_rcu — the INVOKE re-attribution lands on the icall
  itself. The callback edge is real; it is now accounted at the
  registration site.

Hub metrics: the c17037-class hub callerWeight 89,956 -> 80,664
(-10.3%), memberFns 5,679 -> 5,675, conflation classes 339 -> 434
(finer quotient); rescuer_thread-style threadfns LEFT the hub member
list entirely. Still resident at 395: multi_cpu_stop,
migration_cpu_stop, softlockup_fn — stop-machine/smpboot channels,
whose fn travels inside structs (family 2/3, not seedable as INVOKE
v1). That is the next tranche, not a failure of this one.

Cost: neutral-to-better. CGPass 204.7s -> 196.7s; per-drain solve
9.4s -> 12.5s on a finer quotient (cell clusters 40.2k -> 53.4k,
roots 45.0k -> 68.3k — the drained hub un-merges memory classes).
Fact mass flat (71.1M -> 70.8M): the hub's other 5,675 members still
carry the class facts, consistent with the over-determination
finding — draining ONE channel family shrinks answers, not closure.

Whole-kernel run with the pinned kernel-summ config + seeds is in
flight; candidate results go to ka-scratch for review before any
baseline pin moves.

### Kernel INVOKE run #1: the ladder catches a soundness hole (2026-07-25)

The first whole-kernel INVOKE run (pinned config + seeds) read as a
triumph at first glance — 5,649,018 -> 5,480,765 pairs (-168,255,
-3.0%), added set = exactly the 2 vetted wakeme_after_rcu
re-attribution pairs, removed targets = the threadfn drain at 3,320
sites each. The tell was one level deeper: resolved icalls 16,532 ->
16,526, and the 6 fully-drained sites were all inside
smpboot_thread_fn — whose baseline targets included REAL callbacks
(cpuhp_should_run, run_ksoftirqd). smpboot_thread_fn itself went from
3,320 icall-target sites to ZERO. Real loss, not drain.

Root cause, two layers (commit 16ab7dc):
1. The three allocator-branch callers of applySummaryAtoms discarded
   the needPooled return — a dynamic-fn registration through a
   FRESH+INVOKE function (kthread_create_on_cpu passes its OWN FORMAL
   to kthread_create_on_node) wired nothing. Fixed by extracting
   handleCall's actual->formal wiring into wireCallArgs() and calling
   it on fallback (args only; the fresh object stays the ret identity).
2. Even wired, the args fed a SKIPPED body — FRESH routes the callee
   through the allocator body-skip, severing the create-struct ->
   kthread() container channel. Fixed by summaryInvokeKeepsBody():
   INVOKE-bearing FRESH summaries keep their bodies analyzed; constant
   callsites still don't feed them, so the body carries exactly the
   dynamic-registration residual.

Micro pin: t_pairs2.c (FRESH+INVOKE table registration + a wrapper
passing its own formals) — 4/4 exact after the fix, cb3 resolved via
the pooled residual only.

km re-run (fixed): 80,531 -> 71,372 (-9,159, -11.4%); added = the 2
wakeme pairs only; smpboot_thread_fn RESTORED at its 395 pooled
sites, plus the cpuhp-adjacent flows that rode its td channel
(vmstat_cpu_*, takeover_tasklets, slub_cpu_dead, ...). The drain
number is 496 pairs smaller than the broken run — that delta was
exactly the unsoundness.

Method note for the paper: the both-directions diff review plus the
resolved-icalls count is what caught this — the top-line pair delta
and even the added-set review looked perfect. A fully-drained icall
whose baseline held confirmable true targets is the signature that
separates "channel re-attributed" from "channel severed".

Refinement queued: kthread_create_on_cpu is itself a constant-fn
registration API (smpboot passes smpboot_thread_fn constantly) —
seeding it with INVOKE(arg0:f0<-arg1) FRESH would drain the smpboot
residual too. Same for other kthread_create_on_node wrappers.

Kernel re-run with the fixed binary in flight; candidates to
ka-scratch, baselines untouched pending review.

### Kernel INVOKE re-run (post-fix): clean verdict (2026-07-26)

Fixed binary (16ab7dc), pinned config + seeds: 16,532 resolved icalls
/ 5,484,521 pairs vs the kernel-summ pin's 16,532 / 5,649,018 —
-164,499 removed, +2 added (-2.91%). Every soundness tell from run #1
is green: resolved-icalls count restored exactly; smpboot_thread_fn
remains a target at its full 3,320-site pooled residual AND its own 6
icalls carry 436 pairs (== baseline, cpuhp/ksoftirqd true targets
intact); the only additions are the 2 vetted wakeme_after_rcu
re-attribution pairs. Removed = the kthread threadfn fan-in (3,320
sites per threadfn) plus the irq/timer/rcu pools. LEDGER: 464 INVOKE
bindings, 2,258 dynamic-fn pooled fallbacks. Cost unchanged (~2.6h,
dump-dominated). Candidate pin files:
ka-scratch/kernel-invoke2-{stats.txt,icalls.sort.gz} — awaiting
review before replacing the kernel-summ baseline.

### INVOKE candidate census, tier 1 (km, 2026-07-26)

Kernel pin promoted first: test/baselines/kernel-invoke-* is now the
canonical whole-kernel baseline (16,532 / 5,484,521; commit 1b2222d).

--cfl-census-invoke (6e41c7e) makes candidate discovery mechanical:
four body shapes (DIRECT / FIELD / COSTORE / PASSTHRU) filtered by
constant-Function evidence at direct callsites. km: 6,788 functions
scanned, 3,968 raw shape hits, 46 survive the evidence filter — the
filter is doing the work (99% of shape hits are generic container
stores with no fn-registration evidence).

The 46 split into four buckets:
1. Already modeled, rediscovered (validation): __static_call_update
   (task #14), tracepoint_probe_register[_prio] (tp_func machinery) —
   do NOT seed blindly; the data-correlation half may still be worth
   adding on top of the dispatch model, separately evaluated.
2. Deferred registration, new: stop_one_cpu_nowait (FIELD, 8 const)
   and the stop-machine/smp family (stop_machine_cpuslocked,
   smp_call_on_cpu, work_on_cpu_key, smp_call_function_many_cond) —
   this is the multi_cpu_stop/migration_cpu_stop hub residual the km
   A/B left standing. kernel_thread/user_mode_thread/
   __kthread_create_on_node extend the kthread family.
   call_rcu_tasks_generic is the shared body behind the seeded
   call_rcu_tasks wrappers.
3. Synchronous higher-order fns: event_function_call (15),
   perf_iterate_sb (12), task_call_func, kref_put, write_cache_pages,
   parse_args, kallsyms iterators, __bfs — these drain shared-formal
   conflation (the c17037 channel is pointer formals) rather than a
   container pool.
4. PASSTHRU composition: kthread_create_on_cpu INVOKE(arg0:f0<-arg1)
   derived from its single forwarding callsite into summarized
   kthread_create_on_node — the smpboot-residual closer, found
   without hand analysis.

Next: tier-2 confirmer (--cfl-confirm-invoke) applying the #17
completeness discipline (every pointer formal accounted or reject to
LEDGER) so buckets 2-4 can be auto-emitted as reviewed summary lines;
then seed tranche 2 (stop-machine family + kthread_create_on_cpu) and
re-ladder.

### Tier-2 confirmer: --cfl-confirm-invoke (2026-07-26)

Auto-confirmation where the proof is local (commit 7ba1fd7), #17
completeness discipline: DIRECT (fn formal invoked synchronously with
other formals; benign-use walker for everything else; pointer escapes
/ ptr returns reject) and PASSTHRU (translation through an
already-summarized INVOKE callee, +FRESH when the wrapper returns the
callee's fresh result; wrapper-chain fixpoint). FIELD/COSTORE remain
census-REVIEW: their dispatchers live elsewhere, no local proof.

Micros: t_pairs3.c — run_cb auto-confirms, cb pairs exact, dispatcher
drained; run_cb_leak (data escapes to a global) rejects esc-store and
stays pooled (sound). t_pairs2 — spawn_wrap auto-confirms PASSTHRU
+FRESH. (Micro note: -O1 funcspec cloned the HOFs per callsite and
trivialized the baseline; t_pairs3 is built at O0+mem2reg.)

km A/B (pinned config + --cfl-confirm-invoke, vs km-invoke2 71,372):
13 auto-confirmed (8 DIRECT + 5 PASSTHRU, 3 rounds): the iomem/RAM
walker family (walk_system_ram_range/_res/_rev, walk_mem_res,
__walk_iomem_res_desc + PASSTHRU walk_iomem_res_desc),
kthread_create_on_cpu (+FRESH — the predicted smpboot closer, derived
not hand-seeded), request_any_context_irq (via request_threaded_irq),
get_device_system_crosststamp, kallsyms_on_each_symbol,
for_each_kernel_tracepoint, hibernate_quiet_exec,
bpf_dispatcher_nop_func. Rejected to LEDGER: 37 escape, 4 ptr-ret,
1 no-binding, 4 mixed-shape — the tier-3 proposer's review queue.

Answers: -397 pairs / +0. 395 = smpboot_thread_fn leaving the pooled
smear entirely; its own 6 icalls SHARPEN from 436 pool-smeared pairs
(85-target smear incl. cpuhp state callbacks) to 101 pairs carrying
the true smp_hotplug_thread population (cpuhp_should_run,
cpu_stopper_thread, cpu_stop_should_run, ...) — per-registration td
binding replacing the kthread data pool. The remaining 2 = walker-
family data precision.

Adoption path (per the recorded rollout discipline): the 13 CONFIRMED
lines are file-format; adopting them into func_summaries.txt (the
reviewed artifact) + kernel re-pin is the next decision point.
--cfl-confirm-invoke itself stays OFF in pinned configs.

### Tier-3 input: kerneldoc corroboration (tools/kdoc_invoke.py, 2026-07-26)

The 13 tier-2 lines were adopted into func_summaries.txt (4630c6a; km
file-only run byte-identical to the confirmer run, 70,975); kernel
re-pin candidate in flight.

The kernel documents the INVOKE relation in stereotyped kerneldoc:
"@dev_id: A cookie passed back to the handler function"
(request_threaded_irq) is INVOKE(arg1:f1<-arg5) in natural language.
tools/kdoc_invoke.py (5a7542e) cross-checks census candidates against
these idioms: ordered @param blocks give doc-implied fn/data indices;
agreement with the census-derived indices emits a proposal line
carrying the matched doc sentence as provenance; disagreement emits
PARTIAL. Docs describe intent — proposer tier only, confirmer/file
review remain the gate.

km residual queue (40 after adoption): 3 AGREE (task_call_func
"Argument to function." -> INVOKE(arg1:f1<-arg2); write_cache_pages
"data passed to writepage function" -> INVOKE(arg2:f2<-arg3);
stop_one_cpu "argument to @fn"), 7 PARTIAL (incl. the
tracepoint/stop-machine families where the doc names the fn but the
data phrasing is loose), 22 no-doc. The no-doc population is
internal/static helpers (__static_call_update, event_function_call,
__bfs, __kthread_create_on_node): the kernel documents its PUBLIC
boundary. Evidence sources therefore complement BY LAYER — body proof
for internals, callsite evidence everywhere, documented intent at the
API boundary — each gated by the one above it. (Paper: a three-source
evidence pipeline of decreasing rigor with a single soundness gate.)

### Tier-3 review + adoption: the LLM tranche (2026-07-27)

All 38 kerneldoc-mined proposals reviewed against 6.8.2 signatures and
callback typedefs under the completeness rule. ADOPTED 15 (a075227):
irq cookie family (incl. devm_request_threaded_irq with BOTH handler
and thread_fn — the LLM only proposed handler; and request_nmi/
request_percpu_nmi the census never saw), async_schedule family,
stop-machine family, smp_call_function_single/any (single's LLM
off-by-one corrected against kerneldoc order), task_call_func (both
formals). REJECTED 15 with reasons recorded in func_summaries.txt —
the two recurring rejection classes are exactly the atom's current
expressiveness limits: (1) callbacks receiving BODY-DERIVED pointers
(write_cache_pages' folio, allocate_resource's candidate resource,
mempool elements), (2) callbacks receiving a CONTAINER/ret object
holding the data (sys_off_data, subprocess_info, hw_breakpoint
event). Both are future-atom material (deref-binding / ret-binding),
not adoption failures. Plus one genuine trap the review caught:
alarm_init also installs alarmtimer_fired into the data formal's
embedded hrtimer — summarizing would sever a second callback channel.

km A/B: 70,975 -> 69,080 (-1,895/+0). Removed = the stop-machine
residual the tier-2 verdict left standing (softlockup_fn,
push_cpu_stop, __balance_push_cpu_stop, active_load_balance_cpu_stop
each leaving 395-site pools) + the 31-site smp/IPI pool
(remote_function, rcu_exp_handler, __perf_event_read, ...). With this
tranche the c17037-class hub's remaining 395-fan members are down to
the family-2/3 store-side idioms (workqueue/timer/ops containers).

Kernel run for the kernel-llm-invoke pin in flight (pre-approved,
pinned on a clean both-directions diff). Cumulative #28 arc at km:
80,531 -> 69,080 (-14.2%) across hand seeds + tier-2 auto-confirm +
tier-3 doc-mined adoption, every step -N/+0 or +2-vetted.

### PIN: kernel-llm-invoke (2026-07-27, e73f030)

test/baselines/kernel-llm-invoke-stats.txt is the canonical
whole-kernel baseline: 16,529 icalls / 5,452,202 pairs. Tier-3 kernel
delta vs the tier-2 state: -28,989/+0 — the stop-machine callbacks at
their full 3,320-site pools and the async_schedule population
(async_suspend*, attach_async helpers, do_populate_rootfs, ... at
547-site pools; the async pool is far larger at kernel scale than km
suggested). One resolved-icall drop = task_call_func's own dispatcher
(constant-registered re-attribution, verified). Cumulative #28 arc at
kernel: 5,649,018 -> 5,452,202 (-196,816, -3.5%); at km: 80,531 ->
69,080 (-14.2%). Every adoption step -N/+0.

### Family-2/3 field-channel census (task #29, km, 2026-07-27)

--cfl-census-fields measures the store-side registration channels:
(struct,byte-offset) keys with constant-Function stores on one side
and field-load-fed icalls on the other, plus paired sibling-store
evidence. km: 631 field keys, 37 two-sided channels, 100 store-only,
465 load-only; 340 constant-fn stores, 1,539 field-load icalls.

Two findings that shape the design:

1. TYPE NAMES ARE GONE AT -O2. The dominant "channel" is ?+0 — 44
   constant-fn stores / 3,095 dynamic ptr stores / 423 dispatch loads
   whose GEPs are i8-canonicalized (opaque pointers): struct identity
   is unrecoverable from the IR access path for most of the corpus
   (notifier_block.notifier_call lands here — sys_off_notify in the
   sample). Any family-2 model keyed on struct types would cover only
   the typed minority; the correlation carrier has to be the OBJECT
   (origin), not the type. That is exactly what the flows-to
   (origin,shift) planes already track — reinforcing the original
   design note that family 2/3 is same-origin binding, latent in the
   existing fact machinery.
2. THE PAIRING IS REAL. Where types survive, the (fn,data)
   sibling-store correlation is near-total: rmap_walk_control 11/11
   paired, remote_function_call+8 11/11, balance_callback+8 8/8,
   cpu_stop_work+16 (multi_cpu_stop — the stop-machine container
   itself), hrtimer+40 6 stores (the hrtimer_init family the INVOKE
   census could not see), task_struct+1336 restart_block 14 stores,
   callback_head+8 task_work. Stack-allocated ops structs
   (rmap_walk_control, remote_function_call) are per-callsite objects
   — same-origin binding would resolve them exactly with NO new
   summary vocabulary.

Design direction recorded for the solver lever: at icall wiring,
partition the fptr class's function facts BY THE ORIGIN they traveled
through (the witness-exact unification machinery already certifies
which joins carried a fact) and bind the receiver/data operand
per-origin instead of pooled. Cheap-atom complement for the untyped
registration side: a deref-binding INVOKE variant (fn read from
*argD+off — the notifier shape) for registration APIs whose fn
arrives inside the data container.

### Falsification #6: same-origin binding is vacuous on the final quotient (task #29, km, 2026-07-27)

--cfl-probe-origin-split compares, per load-shaped icall, the pooled
answer against the counterfactual origin-indexed answer (targets
present in the merged cluster classes of the container origins the
fptr was loaded from). km verdict, all resolution rounds: 1,047
load-shaped icalls probed (426 non-load fptrs), pooled 63,304 pairs
vs origin-indexed 63,304 — 0.000% excess — and cluster diversity
D==1 for EVERY SINGLE icall. All container origins reaching any given
fptr load have already collapsed into one merged cluster class by
fixpoint.

Reading: the (fn,data) correlation the field census showed on the
STORE side (rmap 11/11 paired, etc.) is destroyed by the time the
solver converges — the pooling happens IN the cluster merges (exact-
fact joins are transitive, so cells sharing any flow unify), not at
the icall wiring. Same-origin binding as a wiring-time refinement of
the final state is therefore worth exactly zero: there is no origin
partition left to exploit. Consistent with fs13==FI on harfbuzz
("classes merged before planes can discriminate") and the
over-determination finding — this is the same phenomenon measured a
third way, now at the origin level.

Consequences for the roadmap:
- The correlation lever for family 2/3 must act BEFORE or AROUND the
  merges: (a) provenance-preserving machinery (per-field memory
  cells / witness-indexed facts — the known big-ticket redesign), or
  (b) bypass the container entirely on the registration side — the
  deref-binding INVOKE atom (fn read from *argD+off, notifier shape),
  which drains channels the way family 1 did, no solver change.
- (b) is the near-term play; (a) is the paper-scale rework whose
  justification this probe now makes falsifiable and quantified.

### Keyed pair-channels: CHAINREG/CHAINCALL (task #29, 2026-07-27)

The sound deref-binding design (9476849): a registration-only INVOKE
on notifier chains would sever the dispatch-time data argument, so
the model pairs both sides per chain-head key — CHAINREG reads the
callback from the block global's const initializer; CHAINCALL records
dispatch sites; finalize wires the per-key cross product with the
callback attributed AT THE DISPATCH SITE and both data channels bound
(self <- block, fN <- dispatch argV). Micro-exact (t_chain.c: per-key
2 pairs vs pooled 6). All fallbacks pooled + LEDGERed; orphan keys
keep their pooled channel — severing impossible by construction.

km A/B: NULL RESULT, kept honest — 3 const registrations and 25
dispatch sites share no keys at km scale; 18/21 registrations are
wrapper-mediated (register_foo_notifier passes its formal, so the
block is dynamic at the CHAINREG callsite). The notifier ecosystem's
correlation lives one wrapper level up, where the KEY is constant
inside the wrapper body. Next increment: global-keyed CHAINREG
(key in the atom's gsrc slot) + the tier-2 composition lift deriving
it mechanically from wrapper bodies — then re-measure at km and
kernel scale, where the register/dispatch key overlap should be
dense (reboot/netdev/cpu chains all have both sides in-corpus).

### Chain lift lands + a general drain bug found (task #29, 2026-07-27)

Commit 967618b, three pieces: canonical chain keys (GUID -> def; raw
GlobalValue* pointers never matched across TUs), the CHAINLIFT
composition rule (wrapper forwarding its block formal into a
CHAINREG callee with a body-constant key inherits the global-keyed
atom; CHAINCALL sites always keep pooled wiring — pairs are additive,
so fallback registrations and manual chain links can never be
severed), and a GENERAL bug the lift micro exposed:
globalDedupScanCallEdges pre-merged single-callsite actual<->formal
node pairs, making every summary drain silently vacuous for
single-caller summarized functions. Two ablations (self-bind edge,
Callees insert) exonerated the finalize wiring before the union-find
pre-merge emerged as the only remaining channel. Dedup now skips
summarized callees. All prior INVOKE results were sound but
conservatively over-approximated at single-caller wrappers — the
kernel re-run quantifies the recovered drain.

km (confirm-invoke on): 8 CHAINLIFT wrappers derived by name
(register_reboot/pm/module/oom/vmap_purge/restart_handler/
pvclock_gtod/mt_adistance), 17 const registrations x 25 dispatch
sites over 4 keys -> 66 wired pairs; 69,080 -> 68,563 (-517/+0).
Micros exact (t_chain3 1-pair drain, t_chain2 2/2). Kernel run in
flight; pin refresh awaits review.

### PIN REFRESH: kernel-llm-invoke (2026-07-28, 061a4d4) — task #29 closed

16,516 icalls / 5,444,041 pairs, confirm-OFF file-only config. vs the
2026-07-27 pin: -8,220/+60 — notifier keyed pair-channels (42 regs x
107 dispatch sites over 10 keys, 125 pairs) + dedup-drain recovery at
single-caller summarized wrappers + the vetted bpf_throw addition +
a 59-pair __SCT__tp_func_nvme_sq residual (definition-less trampoline
declaration-selection nondeterminism across binaries; known class).
Option-b file expression needed TWO fixes caught by the adoption
identity check: GUID-map resolution for external chain heads and a
unique local-linkage scan for static heads. Remaining #29 frontier ->
new tasks: family-3 ops structs; provenance-preserving cells
(big-ticket, motivated by falsification #6). Kernel kdoc corroboration
of the 251-item confirmer rejection queue was NULL (165 no-doc,
internal helpers) — the doc tier is exhausted below the API boundary.

### Family-3 two-level ops census (task #30, km, 2026-07-28)

--cfl-census-fields now reports OpsChannels: two-level dispatch
(obj->ops then ops->fn feeding an icall) with receiver evidence. km:
416 channels / 853 dispatch sites, 386 (45%) pass the receiver (the
inner load's base object) as a callback argument; 54 distinct ops
globals stored. Top channels are the canonical kernel vtables, most
WITH receiver correlation: sched_class via task_struct+688,
dentry_operations via dentry+224, vm_operations_struct via vma+120,
trace_event_class via trace_event_call+16, bpf_map_ops, mm_walk_ops
(all recv==sites); irq_chip via irq_desc+64 and pmu channels show
recv=0 only because the receiver is a SIBLING field (&desc->irq_data)
— the exact-base test undercounts those.

Reading for the model (task #30 step b): the keyed ops-channel shape
is real — key = the ops GLOBAL (54 of them), registration = ops-ptr
store into a container origin, dispatch = the 386 receiver-passing
sites. Callsite-level pairing (the chains precedent) bypasses the
cluster merges falsification #6 forbids exploiting. The complication
vs notifier chains: registration stores are NOT behind one API — they
are raw field stores (family-2 shape) — so the registration side
needs either a store-pattern recognizer (census already finds them)
or per-ops-global Callees pairing at the dispatch sites directly
(ops-global -> its member fns is STATIC from the initializer; the
pairing question is only WHICH receivers, which is where the
container origin enters). Design continues next session.

### OpsMono instrument: site-level containment is the wrong certificate (task #30, km, 2026-07-28)

--cfl-probe-ops-mono classifies two-level dispatch sites by target
containment in one ops-global member set. km: 701 sites — 23 mono
(3.3%), 37 near, 620 polymorphic (88%), vs 988 ops globals (>=2 fns).
Poly giants: bpf_iter_create |T|=483, move_to_new_folio |T|=339.

READING: this does NOT refute kernel modularity — it shows SITE-level
containment is the wrong granularity for the certificate. A vfs/bpf
dispatch site legitimately serves many ops globals (many drivers/map
types through one site); modularity lives at the PAIR level (each
receiver with the members of ITS OWN installed g). The 23 mono sites
are the only ones where per-g pairing is free; everywhere else the
model must be per-pair: bind each member fn F of g's RECEIVER FORMAL
to the origins g was stored into (store-side IR evidence, pre-merge,
so falsification #6 does not apply) — a callee-side constraint
tightening, not site partitioning. Soundness needs a per-g
completeness bit (every store of g base-resolvable; container
copies/memcpy escape-hatch to pooled). That per-pair model + its
completeness discipline is the next design block for #30.

### Step 2 lands + two findings: a constexpr-GEP soundness hole and the cell-merge wall (task #30, 2026-07-28)

Step 2 (receiver-formal tightening) is implemented: at a two-level
dispatch site (fptr = load(gep(load(gep(recv))))), a resolved callee F
that passes opsFnTightenable — member of >=1 table, ALL tables holding
F certified, and F's address never escaping outside certified-table
initializers (direct calls and compares are the only other allowed
uses) — has its receiver formal bound to the certified containers of
every table holding F, and the pooled receiver-arg edge is skipped
(handleCall/wireCallArgs thread a skipArg). Everything else stays
pooled; LEDGER: g_opsTightSites/g_opsTightRej.

The micro (test/t_ops.c: OA/OB carry certified ops_a/ops_b, shared
dispatcher o->ops->op1(o), inner icall o->cb()) surfaced two facts:

1. SOUNDNESS HOLE (pre-existing, fixed): in field-insensitive mode a
   non-zero-field ConstantExpr GEP gets its own node (NodeFactory
   gepMap keyed (base, fieldNum)) and NOTHING emitted the grammar's
   GetElementPtr base->result 'a' edge — ensureConstGEPFieldEdges
   early-returned unless field labels were on. Every store/load
   through gep(@G, field) in instruction position was silently severed
   from @G's cell: t_ops inner icalls resolved to NOTHING (0 targets)
   while type-based saw 8 pairs. Fix: getRepNodeForValue now calls
   ensureConstGEPFieldEdges in all modes; without field labels it
   emits the plain assignment edge. Existing micros + smoke unchanged
   (none exercised the pattern); km/kernel A/B = soundness additions
   expected.

2. THE CELL-MERGE WALL (t_ops, post-fix): tightening fires exactly as
   designed (2 tables certified, 4 (F,recv) wirings, 0 rejections) and
   the inner icalls STILL smear {cba,cbb}. TRACE-BWD shows why: the
   genuinely-polymorphic dispatcher's ops-load witnesses BOTH (OA,0)
   and (OB,0), and witness-exact unification makes that load's class
   the shared representative of both cluster keys — every subsequent
   single-witness reader (a1's cb-load joining (OA,0)) merges into the
   same class and inherits the union. The receiver formal IS correctly
   restricted to OA; the read-through re-smears at the quotient. This
   is falsification #6's mechanism operating at the cell layer, and it
   gates the entire per-pair payoff: wiring-side tightening is
   necessary but NOT sufficient. The missing mechanism is
   provenance-preserving cells — protected (origin,shift) cluster keys
   whose readers copy facts out (the solver's existing non-transitive
   bridge primitive) instead of unifying, with writers still merging
   in. Scoped to certified containers this is bounded; it is the
   concrete next design block, and t_ops is its acceptance test
   (a1->cba only, b1->cbb only, dispatch unchanged).

### km verdict, step 2 as-wired: the wall is real (task #30, 2026-07-28)

km A/B (--cfl-ops-pairs vs without, both on the GEP fix): 629 (F,recv)
wirings tightened, 40,734 two-level rejections, and the answer diff is
0 removed / +22 added (traceiter sites +1 each, second-order flow from
the container->formal edges). Exactly what t_ops predicted: under
witness-exact cell unification, receiver-formal tightening removes
NOTHING (reads re-smear at the quotient) and its added edges can only
add. --cfl-ops-pairs therefore stays OFF in the pinned config; the
certificates + wiring are the instrument half of the mechanism, and
the payoff is gated entirely on provenance-preserving cells (protected
cluster keys, reader-copy via the bridge primitive). t_ops is the
acceptance test.

### Provenance-protected cells v0 SHIPPED + kernel pin refresh (task #30, 2026-07-29)

The protected-cells prototype landed inside --cfl-ops-pairs: certified
container origins key protected cluster entries; WRITER cells (any
in-edge, tracked in a protIn class-folded copy of hasIn) merge into
the per-origin cell exactly as before; READER cells bridge (the
solver's non-transitive pairwise exchange — facts cross once, re-emit
native along a-edges, never re-cross another bridge); readers arriving
before any writer wait and attach when the cell materializes; a
bridged reader that later gains an in-edge (merge fold or incremental
wiring) is DEMOTED — merged into every cell it bridge-joined. All
LEDGERed (ProtCells line).

t_ops ACCEPTANCE PASSES: a1->cba, a2->cba, b1->cbb, b2->cbb — per-pair
exact, dispatch unchanged, 2 cells stay distinct classes, 0 demotions.
The mechanism trilogy (certificates -> receiver tightening -> protected
cells) delivers the user's pair-precision recovery on the micro. Full
micro suite without the flag: bit-identical (feature inert). With the
flag: the ONLY movement across all micros is t_ops's 4 cross-pair
removals. Smoke 4/4.

km reality check: 39 protected origins (of 102 containers — globals
whose value class minted a root), 91 writer merges COLLAPSE them to 8
distinct cell classes, 17 reader bridges, 0 demotions — and answers
are IDENTICAL to ops-pairs-without-protection (128,249). The km-scale
payoff is gated on certificate COVERAGE, not mechanism: shared
registration writers (one helper's deref cell joins many protected
keys) merge cells pairwise, exactly the predicted multi-key writer
collapse. Levers, in order: (1) walker v2 — recurse one level into
call arguments under PASSTHRU discipline (relay_open/cdev_init class,
the dominant 226-incomplete bucket) to certify more globals AND to
break shared-writer collapse by certifying the helper's formal
channel; (2) per-container writer splitting at the helper (same
formal-channel evidence).

KERNEL PIN REFRESH (canonical, flag OFF): 18,189 icalls / 8,389,759
pairs, -59 (all the documented __SCT__tp_func_nvme_sq trampoline
nondeterminism) / +2,947,968 vs the prior pin — 51% tracepoint probe
pools, the rest kvm_x86_ops/x86_pmu-style constexpr-GEP ops-struct
traffic. 4.12 h (+53%). test/baselines/kernel-gepfix-stats.txt.

### Walker v2: one-level call-arg recursion + benign-read recovery (task #30, 2026-07-29)

certifyOpsPairs v2, three extensions under the same completeness
discipline: (1) benign interior reads — direct member loads of a table
(and load-only GEP/constexpr chains) no longer fail the certificate;
(2) one-level recursion into a direct callee's formal when &g escapes
as a call argument: the recipe classifies every use of the formal
(member reads/compares benign; store into formal k's field ->
container = caller actual k; store into a global -> that global; store
into a call-result local returned on every path, incl. the mem2reg
phi-of-{B,null} shape -> container = the callsite value; second-level
calls/unresolved bases FAIL); (3) read-only tables (never stored)
certify with an EMPTY container set — sound (they can never sit
behind a two-level receiver) and it unblocks opsFnTightenable for
members shared with stored tables.

Micro t_ops2.c (reg_ops = cdev_init shape, mk_widget = relay_open
ret-alloc shape, direct_probe = benign read): both tables certified, 3
containers (OA, OB, callsite value), 0 incomplete. t_ops regression:
still per-pair exact. Micros without the flag bit-identical; smoke 4/4.

km: certified 93 -> 161 (+60 read-only, +8 call-escape recipes, 1
ret-alloc), incomplete 226 -> 158; remaining rejections: 56
no-body/vararg (the helper defs live OUTSIDE the kernel/-only km
subset — full-kernel runs will resolve most), 9 second-level, 8
base-unresolved, 1 other. Answers IDENTICAL (128,249) and ProtCells
unchanged (39 origins / 8 classes): the new certificates are read-only
(no containers) or carry non-global containers (v0 protection is
globals-only), and the shared-writer collapse still owns the km
subset. t_ops2 demonstrates the collapse at micro scale: reg_ops's
single store cell joins both protected keys as a writer and merges
them — certificates fine, cells collapsed.

NEXT (the payoff unlock): store-side splitting through the EXISTING
summary machinery. A helper whose recipe proves BOTH formals fully
replicable (table formal j only stored; container formal k only
stored-into with replicable values) is exactly an ST atom
("H ST(argK <- argJ)"): applySummaryAtoms wires it per-callsite and
skips the pooled formal channel — distinct writer cells per container,
which protection then keeps separate. Plan: auto-PROPOSE such lines
from the recipes (tier-2 confirmer pattern), review, adopt into
func_summaries.txt. Helpers that do more (cdev_init's kobject_init
call) correctly fail the both-formals test and stay pooled.

### ST-proposal pipeline + backward-closure protection: the arc closes on micro (task #30, 2026-07-29)

Three pieces landed:

1. --cfl-propose-ops-st: whole-body qualifier over the call-escape
   helpers from the certification walk. A helper qualifies iff EVERY
   instruction is per-callsite replicable (formal-base stores of
   pointer-formal/null/scalar values — scalar formals need no atom;
   non-pointer reads; pointer loads only null-checked; no
   formal-derived call operands; ret void/scalar/formal->ALIAS).
   Output is adoptable func_summaries.txt syntax, proposals only.

2. Backward a-closure protection seeding: protecting only container
   VALUE classes was insufficient — t_ops2's readers co-witness the
   helper's heap origin (minted on the alloc callsite class INSIDE
   mk_widget), merge through that unprotected key, gain in-edges from
   the helper's stores, and the demotion cascade collapsed both
   protected cells. protCls now closes backward over static a-edges
   (depth 8 / 8192-class cap, partial closure = weaker protection
   never unsoundness) and mintRoot protects roots minted mid-fixpoint
   on closure classes (FRESH heap origins).

3. t_ops2 END-TO-END EXACT with reg_ops's proposed summary adopted:
   3 protected origins / 3 distinct cells / 0 demotions, a1/a2->cba
   only, b1/b2->cbb only. The full mechanism chain — certificates ->
   receiver tightening -> ST severing -> protected cells — delivers
   the pair-precision recovery. Ladder: micros no-flag bit-identical,
   t_ops 0 cross-pairs, smoke 4/4.

km reality: 973 protected origins now (39 before closure), but STILL
14 distinct cells / 184 demotions / answers identical (128,249; +12%
runtime) — km's registration writers are pooled formal channels of
UNSUMMARIZED helpers, and the subset only surfaces ONE qualifying
proposal: bpf_link_init ST(*arg0<-arg2) ST(*arg0<-arg3) (reviewed
against kernel/bpf/syscall.c: pure setter, scalars atom-free; ADOPTED
into func_summaries.txt; km adoption A/B 0/0 — answer-neutral in the
canonical config, kernel identity check rides the next full run). The
volume target is the 56 no-body rejections — cdev_init, relay_open
and friends are defined OUTSIDE the kernel/-only km subset, so the
proposal sweep must run at FULL kernel scale next; adoption there
feeds both the summary drain (INVOKE-style) and the protected-cell
separation under --cfl-ops-pairs.

### Kernel OOM -> self-limiting protection (task #30, 2026-07-29)

First full-kernel --cfl-ops-pairs run died OOM entering iteration 1 —
but iteration 0 is a trove: 1,103 tables certified (589 embedded, 260
read-only, 128 call-escape recipes), 178,416 tightened wirings, and
kernel-scale certification surfaced the failure mode: 9,387 protected
origins collapse (11,348 writer merges, 4,625 demotions) into 18
mega-cells, and ~12.6k reader BRIDGES each materialize a private copy
of a mega-cell plane. Copy-not-unify's cost lands precisely where the
mechanism has already lost discrimination.

Fix: self-limiting protection. A cell class anchoring > K=4 protected
keys is marked COLLAPSED: its bridge partners are merged back in and
future readers merge (plain pooled semantics for that family) — no
per-reader plane copies where there is nothing left to separate.
Anchor counts are per-class, folded through merge (queued collapse
processing, no reentrant merges). km: 1 collapse / 718 readers
pooled, demotions 184 -> 54, runtime 269 s -> 175 s (cheaper than the
UNlimited run), answers stable. Micros exact, 0 collapses.

Kernel sweep relaunched with the limiter (kernel-stprop2.log).

### Kernel-scale verdict: task #30 closes — certificates prove modularity, ONE store-hub absorbs it (2026-07-30)

The relaunched kernel sweep completed (4.43 h, +7.5% over baseline, no
OOM — the K=4 limiter held: 1 collapse, 80,782 readers pooled).

The numbers:
- Certification at kernel scale is RICH: 1,103 tables certified (589
  initializer-embedded, 260 read-only, 128 call-escape recipes / 6
  ret-alloc), 1,110 containers, 835 incomplete. 178,416 (callee,site)
  wirings tightened. The user's modularity hypothesis is provable
  from IR evidence at scale.
- The payoff is ZERO on the final quotient: answers vs the canonical
  pin = 0 removed / +59 added, ALL the documented
  __SCT__tp_func_nvme_sq flap. ProtCells: 9,802 protected origins
  collapse into 11 distinct classes — ONE connected shared-writer
  component (the kobject/device-init registration universe) absorbs
  essentially every certified container; 42 bridges survive, moving
  nothing.
- Helper-level severing is NARROW under the strict whole-body
  qualifier: 2 of 21 escape helpers qualify kernel-wide
  (bpf_link_init, d_set_d_op — both reviewed against source and
  ADOPTED; both answer-neutral at km, 0/0). The v2 rejection ledger
  says where the volume hides: 180 second-level escapes (wrapper
  chains), 140 base-unresolved, 33 no-body, 33 other.

READING (taxonomy entry): callee-side per-pair binding — even with
sound certificates, receiver tightening, and copy-out cells — cannot
separate what a connected STORE universe has already joined. The
discrimination the certificates prove is destroyed upstream of every
dispatch site by shared registration writers, and severing those is a
summary-COVERAGE problem (each helper needs its store channel
replicated per callsite), not a solver problem. The two adopted
helpers are the existence proof; the 180 second-level rejections are
the next coverage tranche (qualifier recursion depth 2 = wrapper
chains like device_add_disk -> ...), and the INVOKE/CHAINREG family
remains the model for hub channels too entangled to qualify.

DISPOSITION: --cfl-ops-pairs stays OFF in the canonical config
(instrument + acceptance tests + certificates retained; zero-cost when
off). Canonical pin kernel-gepfix UNCHANGED (flag-on run reproduces it
modulo the known flap — that is also the pending kernel identity check
for the two adoptions, now discharged). Task #30 CLOSED; frontier
recorded: (a) qualifier depth-2 wrapper recursion, (b) provenance
cells as first-class solver design (this prototype = the scoped
evidence), (c) tracepoint/kvm_x86_ops keyed channels from the GEP-fix
smear families.

## Instrumentation-sink channels: measurement study (task #31, km, 2026-07-30)

Question (user): the 9,802-origins-into-11-cells collapse is driven by
a connected writer universe — can we model/summarize it? Instruments:
ProtCoalesce blame census now reports per-class characteristics
(members / fact planes / edges / keysAnchored / collapsed), and
--cfl-probe-sink-ablate=<substrs> (MEASUREMENT-ONLY UNSOUND) skips all
cluster joins by cells belonging to matching functions/globals.

### The fusion structure is hub-plus-tail

km, flag-on: 1,001 key-family fusions via just 8 writer classes, and
every blame entry resolves to ONE terminal blob (c16931: 73 members,
35,061 native facts, 967 of 980 protected keys anchored, COLLAPSED).
Pre-merge exemplars split the bulk between the perf/ftrace capture
universe (~649) and lockdep's lock_classes walker (~277). BUT ablating
both hubs (M3) still yields a 959-key blob (c697: 184 members, 25,956
facts, -26% fact mass) built by a 1x-each tail of ordinary shared code
(wait_consider_task, do_kexec_load, sysfs_* ...): killing the hubs
shrinks the blob and recovers separation only modestly (distinct
cells 14 -> 18, reader bridges 26 -> 209). The hubs' real costs are
join traffic, answer smear, and solve churn — quantified below.

### km ablation matrix (all diffs are removals-only, +0)

config                                   joins-skipped  match-CFL  Dpairs   note
M1 baseline (--cfl-ops-pairs)                        0    128,249       0   14 cells, 26 bridges, 54 demotions
M2 + perf_trace_/trace_event_/__bpf_trace_/
     trace_buf/ring_buffer_                131,280,998    112,282 -16,042   registration ablated too — NOT a model target
M3 M2 + lockdep/lock_class/__lock_acquire  135,504,757    112,172 -16,152   lockdep alone: +4.2M joins, -110 answers
M4 payload only (ring_buffer_,trace_buf)    35,639,393    124,657  -3,639   registration INTACT (__traceiter_ pools survive)
M5 payload only, canonical no-flag config   35,639,393*   124,657  -3,617   same tally as M4 — protection-independent

(*same patterns; runtimes 294-430 s under concurrent kernel-run
contention — not comparable beyond "ablation lookup cost is visible".)

### Channel characteristics -> what each construct does to the graph

1. TRACE PAYLOAD CAPTURE (ring-buffer event payloads, trace_buf):
   pointer values stored AS DATA — often ptr->u64 laundering that the
   int-provenance model correctly witnesses (km: 5,368 modeled int
   stores / 8,503 loads; 1,735/5,523 unmodeled-interprocedural in the
   LEDGER). Effect: ~27% of ALL cluster-join traffic (35.6M joins),
   3,6xx pure-smear answer pairs (a 232-target fn pool laundered into
   unrelated sites like vmemmap_pte_entry), and the dominant share of
   protected-key fusions. Payload cells are read by formatters/
   userspace export, not dispatch — the sink-model candidate.
2. PERF/EVENT GLUE WHOLESALE: dominates join traffic (131M) and holds
   16k answer pairs, but perf probe REGISTRATION lives in the same
   functions (perf_trace_* fns ARE tracepoint probes) — wholesale
   sealing removes legitimate probe dispatch (bpf_link_release -563,
   __traceiter_* -232 pools in M2 vs INTACT in M4). Only the payload
   sub-channel is separable.
3. LOCKDEP (lock_classes + walkers): 4.2M joins, ~277 fusions, -110
   answer pairs — nearly pure graph/solve overhead from debug-only
   machinery. Trivial sink model, or gone entirely in a production
   (!CONFIG_LOCKDEP) build.

### Design conclusion (recorded)

The shipped model should be a reviewed SINK family, not ablation:
seal ring-buffer/trace payload CELLS (stores keep their own cell,
joins to stored objects' keys suppressed) gated on a read-back
contract confirmer — enumerate ring_buffer_event_data /
trace_event_buffer consumers and machine-check none feeds a dispatch;
lockdep registration gets the same treatment (compare-only contract).
Expected canonical-config effect at km: -3.6k smear pairs, ~27% join
traffic removed. Kernel-scale blame census running (kernel-blame.log)
to size the same channels + surface driver-core additions before the
confirmer is built. Wholesale perf/event sealing is RECORDED AS
REJECTED (removes legitimate probe dispatch).

### Kernel ProtWriters composition: the writer universe is healthy — the hub is the problem (task #31, 2026-07-30)

Full-kernel pre-merge writer histogram (17,538 writer merges into
protected cells, 2,122 distinct identities; run 2.56 h, answers ==
canonical baseline):

1. THE HUB: 9,767 merges (56%) from ONE class, stable exemplar
   fwnode_graph_devcon_matches::call, plus 5,229 <unnamed> (mostly its
   synthetic satellites) — together ~85%. This is the long-known giant
   a-connected component, ALREADY fused before it touches any
   protected key; it then serially absorbs 9,7xx container families.
   The exemplar is diagnostic: fwnode_graph_devcon_matches /
   fwnode_connection_find_match is an INVOKE-SHAPED HOF — it walks the
   device graph invoking match callbacks (devcon_match_fn_t) and
   POOLS THEIR void* RETURNS; every subsystem's matcher return flows
   into one class, connecting the device universe. That is exactly
   the ret-binding gap recorded at task #28 close ("richer atoms:
   deref/ret-binding for the 15 recorded rejections"): an INVOKE atom
   with RET-BINDING (per-callsite match-fn constant -> direct call
   edge, ret bound to that callsite only) would sever the top hub
   channel at its neck. NEXT DESIGN BLOCK.
2. THE HEALTHY TAIL: 2,120 identities at 1-23 merges each —
   drmm_mode_config_init, init_hw_perf_events, __regmap_init,
   crypto_register_*, neigh_table_init, snd_hda_*, ttm_pool_*,
   bpf_struct_ops, squashfs_fill_super, ... Genuine subsystem
   registration writers pairing a handful of containers each: this is
   the population the pair certificates MODEL, and it needs no fixing.
3. TRACE CAPTURE: perf_trace_*/trace_event_* identities at 5x each
   (78x at iteration 0 incl. perf_trace_initcall_level::inttoptr) —
   small in FUSION volume at kernel scale, but its cost is join
   traffic and smear (km: 27% of all cluster joins, -3,6xx pure-smear
   pairs), so the payload sink model stands unchanged.

CONCLUSION (task #31 measurement phase closed): "disable tracepoints/
lockdep" addresses overhead and smear, not the collapse; the
registration-writer universe is healthy long-tail; the single object
that destroys certified discrimination is the pre-fused hub, and its
top identified channel is a ret-pooling HOF. Priority order for the
modeling phase: (1) INVOKE ret-binding atom + fwnode devcon/
connection-find family summaries (severs the hub's neck channel),
(2) trace-payload + lockdep sink models gated on the read-back
confirmer (bounded, already sized), (3) blob-composition diagnostic
for whatever remains of the hub after (1).

### INVOKE :ret kernel A/B — null result, and an attribution lesson (task #31, 2026-07-31)

Kernel run (flag-on, 4.6 h): answers vs canonical pin = 0 removed /
+59 (the known __SCT__ flap); ProtWriters histogram and fusion count
BYTE-IDENTICAL; FuncSummary LEDGER INVOKE counts unchanged. Root
cause, established from the corpus: there are ZERO callers of
fwnode_connection_find_match in this bclist (usb/typec and usb/roles
are not built) — the adopted atom never fired. The g_sumInvokeRet
counter was also missing from the LEDGER print (fixed; :ret bindings
now reported).

THE LESSON (recorded for the taxonomy): protBlameName names a class by
its FIRST NAMEABLE MEMBER. For the small tail classes (1-23 merges)
that is a faithful channel identity; for the 9,767x mega-class it
merely says "an fwnode instruction is among ~100k members" — a member
name, NOT a causal channel. The "hub neck = devcon ret pooling"
hypothesis was built on that misattribution and is REFUTED-AS-TESTED
(untestable on this corpus; structurally wrong regardless — the blob
forms before and independently of that public API's returns).

Standing state: the :ret atom itself is validated (t_retinvoke exact)
and the fwnode adoption is reviewed-sound — kept (live on fuller
corpora, harmless here: 0/+flap). The causal question — WHAT builds
the giant class — needs a formation-time instrument, not member
names: log the early merge events of classes that grow past a size
threshold (which two classes, via which join key / edge kind, at
which solve phase). That blob-formation diagnostic is the next block;
it subsumes the residual-blob item and directly serves the
provenance-cells design (it names the channels a first-class cell
design must refuse to unify).

### Blob-formation diagnostic: the giant is BORN giant — and it is the field-insensitivity quotient itself (task #31, km, 2026-07-31)

--cfl-probe-blob-formation: clsSize maintained across all merges;
merge events logged while both sides are >=64 members (names faithful
pre-blob); INITIAL (pre-solve) top-10 class sizes with member-function
histograms; final report reconstructs the giant's growth by channel.

km findings:
1. THE GIANT IS BORN GIANT: largest PRE-SOLVE class = 73,614 members
   (final giant 177,574 — 41% exists before any solving; the rest
   accretes mostly via sub-threshold small joins). The in-solve big
   events are the already-sized instrumentation channels (63 events /
   10,572 mass keyed by the perf_trace inttoptr origin; lock_classes,
   printk_rb_static, ftrace_regex_open, tracing_mark_write).
2. WHAT THE PRE-SOLVE BLOB IS: member-fn histogram of the 73,614
   class = handle_mm_fault, copy_page_range, unmap_page_range,
   compact_zone, vm_map_ram, pcpu_get_vm_areas (mm page-table and
   vmalloc walkers), ___bpf_prog_run (309 nodes — the BPF interpreter
   register web), load_module, uprobe_write_opcode, process_fetch_insn
   + globals (console_sem, alarm_bases...). Generic pointer-
   manipulation code whose SSA webs are mutually entangled through
   assignment/GEP cycles.
3. THE READING: pre-solve canonicalization collapses only EXACT
   equivalences (a-SCCs, single-callsite actual<->formal dedup) — and
   under a FIELD-INSENSITIVE abstraction the GEP edge is a plain
   assignment, so pointer-arithmetic loops (page-table walks, BPF reg
   file, allocator internals) are genuine V-equal cycles. The blob is
   not an artifact, a bug, or an instrumentation channel: it is the
   exact quotient of field-insensitivity over pointer-arithmetic-heavy
   code. NO summary, sink model, or protection scheme can split an
   exact quotient — only refining the abstraction can (field-keyed
   GEP edges break the cycles; that is precisely the per-field memory
   nodes / shift-grammar plan, and the provenance-cells design).

This closes the causal chain of task #31: instrumentation channels
(trace payload, lockdep) are real but secondary accelerants; the hub
trunk is the abstraction quotient. The scaling agenda's priority
follows: field-sensitive encoding for the a/GEP layer is THE lever on
the giant class — everything else trims its edges. Kernel-scale
confirmation run in flight (kernel-blobform.log).

### Kernel-scale blob formation: verdict confirmed and sharpened (task #31 CLOSES, 2026-07-31)

Full-kernel probe run (2.45 h): FINAL giant class = 1,116,454 members;
pre-solve core = 494,457 (44%) — at kernel scale the born-giant
quotient spans EVERY subsystem's pointer/buffer-arithmetic code: BPF
JIT (582 member nodes) + interpreter, i915 display/atomic (501/436),
elf_core_dump (455), ext4_fill_super (371), nvme_tcp_recv_skb (328),
e1000_xmit_frame (324), plus .str.* rodata literals (the #25 witness
family, present exactly as the taxonomy predicted).

THE CONTROL CASE: the ZSTD decompressor forms its OWN 5,966-member
pre-solve class — pure data-plane code CAN stay separated — and then
fuses in-solve through alloca-keyed joins (751 mass): its I/O buffer
interface is the bridge. That is the stratum-separation thesis in
miniature: separation is the natural state; enumerable buffer
crossings destroy it.

In-solve accretion channels (286 logged events): the long tail of
payload/buffer keys across subsystems (fwnode endpoint walks 2,965
mass, ZSTD buffers, ext4_fc_replay, maple-tree mas_wr_modify, kvm hv
msr, e1000, acpi resource parsing), instrumentation keys (tracepoint
globals 15k+4.5k via the protection paths, lock_classes 407), and
rodata strings (.str.8 439, .str.3 295). Feeders are uniformly
parser/buffer code (n_tty_receive_buf, btf_check_all_metas,
cgroup1_parse_param, find_module_sections, printk rb).

TASK #31 FINAL VERDICT: (1) the hub trunk is the field-insensitivity
quotient, born pre-solve (44% of the giant), uniform across
subsystems — only abstraction refinement (field-keyed GEP edges) or
stratum modeling can split it; (2) in-solve growth runs through
enumerable BUFFER/PAYLOAD crossings + instrumentation keys — exactly
the crossing set task #32's separation theorem must certify; (3) the
instrumentation sink models (trace payload 27% of km join traffic,
lockdep) remain bounded secondary wins, now folded into #32's stratum
program (trace payload IS a stratum channel). Attribution discipline
recorded: name channels at merge time or at pre-solve census — never
by a finished blob's member.

## Task #32: stratum census + ablate probe, km round (2026-07-31)

--cfl-census-strata (km): 5,556 inttoptr / 3,981 ptrtoint. Phys
buckets: directmap 260+13, vmemmap 224, mm-fn 419+487 — the bridge-fn
list IS the blob's mm walkers (unmap_page_range, copy_page_range,
do_wp_page, gup, migration): the two censuses cross-confirm. Trace
237+641. OTHER 4,416 decomposes into nameable families: scheduler
percpu arithmetic (build_sched_domains/select_task_rq_fair),
___slab_alloc freelist encoding (allocator-INTERNAL — below the FRESH
boundary), the BPF interpreter, kprobe/uprobe fetch, module loading.
164 user-copy sites (126 _copy_from_user).

--cfl-probe-stratum-ablate (km, MEASUREMENT-ONLY): severing all 886
phys-classified inttoptr bridges:
1. The blob BARELY moves: pre-solve giant 73,614 -> 71,221 (-3%),
   final 177,574 -> 176,405 (-0.7%). The quotient's skeleton is plain
   typed-pointer/GEP entanglement, NOT the phys channels — field
   sensitivity remains the trunk lever, unchallenged.
2. THE REMOVALS ENUMERATE REAL CROSSINGS: -216/+0 answer pairs, two
   icalls fully drained, concentrated in isolate_movable_page (50)
   and balloon_page_migrate (8) — the movable_operations family
   dispatches THROUGH struct page (page->mapping->mops), a genuine,
   by-design phys-stratum crossing. The separation theorem is
   therefore NOT absolute: its exception list is non-empty, small,
   and mechanically discoverable — exactly the shape a certificate
   family wants (movable_operations registration is typed and
   enumerable; a reviewed crossing certificate covers it).

Reading for the paper: the probe operationalizes the separation
question — removals = crossing inventory; blob response = how much of
the entanglement is stratum-bridging vs abstraction quotient. km
answer: crossings are rare and nameable (theorem plausible modulo a
short exception list), and the blob is quotient-dominated (the
refinement lever is orthogonal). Kernel-scale probe run queued.

### Stratum taxonomy corrected (user review) + bucket decomposition: CONTENT separation holds at km (task #32, 2026-07-31)

USER CORRECTION, now load-bearing: struct page is the kernel's typed
METADATA for a physical page (it lives in the vmemmap array — a
kernel-object stratum citizen); the worry stratum is the physical
page CONTENTS, exposed only through the direct map (__va /
page_address). The first probe conflated the two.

Bucket-selective ablation at km decomposes the earlier -216:
- directmap ONLY (255 bridges severed): -0/+0. ZERO answers flow from
  page contents into indirect-call resolution — the kernel (at km
  scale) never dispatches through pointers reconstructed from
  direct-mapped contents; every dispatch flow arrives via typed
  handles inside the FRESH/global boundaries. THE CONTENT-STRATUM
  SEPARATION HOLDS EXACTLY at km.
- vmemmap ONLY (218 severed): -158/+0 — futex key walks, migration/
  movable_operations, tracepoint pools: TYPED KERNEL-OBJECT flows
  through page metadata, unsoundly cut by the probe. vmemmap belongs
  to the kernel-object stratum; the earlier "crossing inventory" was
  this misclassification (movable_ops via page->mapping is kernel
  metadata dispatch, not a content crossing).

Paper statement this licenses (km-scale, kernel-scale test pending):
"severing every direct-map content bridge changes zero call-graph
answers" — separation of the control plane from page contents is not
an assumption but a measured property, with the vmemmap metadata
plane correctly retained inside the kernel-object stratum. Kernel-
scale directmap-only run queued after the in-flight combined run
(whose removals must be read as metadata+content conflated).

### Kernel-scale stratum probe (conflated all-bucket): removals = ONLY the metadata family (task #32, 2026-08-01)

Full-kernel combined ablation (2,045 bridges severed, 4.6 h): census
scales cleanly (14,798 inttoptr: directmap 839 / vmemmap 505 / mm-fn
723 / trace 741 / OTHER 11,987; 853 user-copy sites, 727
_copy_from_user). Blob response: FINAL giant 1,113,666 vs 1,116,454
(-0.25%) — kernel scale confirms the quotient verdict.

Answer diff vs canonical pin: -620 / +0, and the ENTIRE inventory is
isolate_movable_page (594) + balloon_page_migrate (26) — the
movable_operations family dispatching through struct page METADATA
(the vmemmap bucket the corrected taxonomy keeps inside the
kernel-object stratum). At full driver scale, NO other family
appeared: no DMA, scatterlist, or io_uring content crossing
surfaced even under the conflated cut. (The km-only vmemmap tail —
futex keys, tracepoint pools — re-derives through redundant paths at
kernel scale and does not show in answers.)

Implication: the kernel-scale directmap-only run (in flight) is
expected -0/+0 — the content-separation theorem holding at full
corpus scale. If confirmed, the paper statement upgrades from km to
the whole kernel: severing every direct-map page-content bridge
changes zero call-graph answers; the only phys-adjacent dispatch is
typed metadata (movable_ops), correctly inside the kernel stratum.

### VERDICT: kernel-scale directmap-only run — CONTENT SEPARATION HOLDS (task #32, 2026-07-31)

Full-kernel run with ONLY the direct-map bucket severed (834 bridges;
config = canonical + --cfl-ops-pairs --cfl-probe-stratum-ablate=directmap;
log ~/fast/ka-scratch/kernel-directmap.log). Result:

  resolved 18,189 icalls / 8,389,759 pairs, converged iteration 4 —
  BYTE-IDENTICAL to the canonical kernel-gepfix pin, including the
  match-by-type tally (57,924,966 / 8,034,673 by CFL).

The per-iteration trajectory is the interesting part:

  it0: 16,689 / 7,399,097   (baseline: 16,692 / 7,400,386)
  it1: 18,157 / 8,356,697   (identical from here on)
  it2: 18,180 / 8,385,864
  it3: 18,189 / 8,389,759
  it4: 0 new — converged

Iteration 0 IS perturbed: the 834 severed bridges remove 3 icalls /
1,289 pairs of early derivations. By iteration 1 the fixpoint has
re-derived every one of them through typed kernel-object paths, and
the trajectories are byte-identical to convergence. So the direct map
is not merely answer-irrelevant at the fixpoint — every dispatch flow
that ever touches it has a fully typed witness path that does not.
The content stratum is REDUNDANT for control flow, not just silent.

Per-pair confirmation (dump completed, CGPass 17,386,938 ms = 4.83 h):
both-directions comm of the dumped answer set vs
kernel-gepfix-icalls.sort.gz = -0/+0 EXACTLY — all 8,391,950 dump
lines byte-identical. Not even the __SCT__tp_func_nvme_sq
declaration-selection flap fired this run. Zero genuine
content-stratum crossings to inventory.

THE THEOREM, now measured at full corpus scale: severing every
direct-map page-content bridge in a 6.8 allmod-scale kernel changes
ZERO call-graph answers. Physical-page contents and the kernel
control plane are separated as computed by the analysis itself — the
separation is a property of the kernel's structure, surfaced (not
assumed) by the solver. Combined with the all-bucket run's inventory
(the only phys-adjacent dispatch = movable_ops through vmemmap
METADATA, kernel-object stratum), the stratum picture for the paper:

  1. page CONTENTS (direct map): zero crossings into dispatch — provable
     separation, now an ablation-certified measurement.
  2. page METADATA (vmemmap/struct page): typed kernel objects; carries
     real dispatch (movable_operations) and must never be severed.
  3. user boundary: 853 copy_from_user-family sites are the enumerable
     gate (crossing-certificate program, pending).

Note --cfl-ops-pairs was ON in this run (as in the strata series) and
the answers still land exactly on the ops-pairs-OFF canonical pin —
consistent with task #30's 0/+59-flap verdict that the flag is
answer-neutral at kernel scale, and this run drew the flap-free side.

### VERDICT: kernel-scale user-copy ablation — USER-BOUNDARY SEPARATION HOLDS (task #32, 2026-08-01)

The user-boundary half of the separation theorem, by the same ablation
methodology as the directmap run: sever the memory edges through which
user-space BYTES enter kernel memory, re-solve, diff. New probe flag
--cfl-probe-usercopy-ablate (MEASUREMENT-ONLY UNSOUND) cuts the task
#23 inline-asm raw-ptr memory closure (handleInlineAsm section 2b) at
exactly two shapes:

  1. copy-body: the `rep movs ~{memory}`-clobber asm inside the IR
     bodies of the from-user copy primitives (_copy_from_user family,
     gated by enclosing-function name) — the SOLE source of the
     *dest <- *src pointer-memory edges under the #23 model.
  2. caller-side get_user: `call __get_user_${N:P}` asm (asm-text
     gated, matches __get_user only — egress __put_user untouched) —
     the register-output load through the user pointer.

What is NOT cut: actual->formal argument edges (pointer-identity
dataflow, not memory content), __put_user/copy_to_user egress, and
every shared helper's asm. The cut is the CONTENT channel only:
after it, a user pointer still flows anywhere it flowed before, but
the bytes it points AT no longer land in any kernel cell.

Kernel-scale sever inventory: 3 copy-body + 329 get_user asm memory
closures (334 raw-ptr derefs). Config = canonical pin config exactly
(--cfl-flows-to --cfl-compositional=false --cfl-bidi-prune
--func-summaries --cfl-dump-icalls, ops-pairs OFF — unlike the
directmap run, NO extra flag differs from the pin, so the severed
edges are the sole variable). Log ~/fast/ka-scratch/kernel-usercopy.log,
CGPass 15,353,234 ms (4.27 h).

RESULT: both-directions comm vs kernel-gepfix-icalls.sort.gz =
  -0 / +59, and all 59 additions are -> __SCT__tp_func_nvme_sq — the
  documented definition-less trampoline declaration-selection flap
  (this run drew the flap side; the directmap run drew the flap-free
  side of the same coin). Distinct dump sites 18,191 = IDENTICAL set
  both runs (comm empty both directions on the site projection).
  Zero removals: severing the user-byte channel takes NOTHING away
  from the call graph — no dispatch pair anywhere in the 8.39M-pair
  answer set depends on memory written by copy_from_user/get_user.

THE THEOREM, user half: bytes copied from user space never become
control flow. Every function pointer the kernel ever dispatches
through has a witness path entirely inside the kernel-object stratum;
the user boundary contributes pointer IDENTITIES (the buffers being
filled) but never pointer CONTENTS that reach an indirect call. Like
the directmap half this is surfaced by the solver, not assumed — and
it is exactly the property CFI/signal-handling folklore asserts
(usermode values must never be branch targets), here derived as a
whole-kernel static measurement.

Stratum picture status: content stratum (direct map) DONE -0/+0;
user boundary DONE -0/+0 (mod flap); page METADATA (vmemmap) carries
real dispatch and must never be severed. Remaining task #32 frontier:
crossing certificates for the 853-site copy_from_user gate inventory
(the census side), field-keyed GEP encoding.

### Usercopy crossing certificate: quotient-drowned at kernel scale — certifiability is gated on field sensitivity (task #32, 2026-08-01)

The positive-direction instrument (--cfl-cert-usercopy, commit
4b33247): tag the same two ingress shapes the ablation severs with
synthetic origin objects U (assigned into the asm's raw-ptr cells),
force-mint them past the bidi/lazy oracles (letting the cone oracle
skip U would pre-decide the question), and inventory which icall fptr
classes carry a U root after solve. Cert rids are matched by MINTED
class — post-merge matching blamed every foreign root whose class
later merged with U (340 false roots from 8 sites on the 2-file
corpus). U never adds a callee (not a function) but its roots add
cluster joins: cert answer sets are never pin-comparable, flag is
mutually exclusive with the ablate probe.

Kernel run (kernel-usercert.log, 2.17 h, no icall dump): 3 copy-body
+ 329 get_user sites -> 62 live cert roots, and the verdict is
unambiguous in its SHAPE:

  16,195 / 18,638 icall fptr operands (87%) test positive — but all
  62 U classes merged into bigger classes, and every per-site count
  is an exact multiple of 16,195 (k x 16,195 for labels covering k
  asm sites). One membership set, shared by every root: ALL 62 U
  classes were absorbed into the same giant class — the 1.1M-member
  field-insensitivity blob (task #31) — and "user bytes reach X" is
  quotient membership, not flow (sample: hsw_fdi_disable
  <- kvm_arch_vcpu_ioctl::get_user, i915 display code "reached" by
  KVM ioctl bytes).

Two real results despite the drowning:

  1. 2,443 icall sites (13%) are certified clean EVEN AT the coarsest
     quotient: their operand classes never meet user bytes no matter
     how much the blob smears. A nontrivial unconditional floor.
  2. The certificate program is now provably GATED on field
     sensitivity: the ablation (edge-level, exact) proves the theorem
     -0/+0, but a nameable crossing INVENTORY at class granularity is
     information-free while the quotient conflates U with the blob.
     Field-keyed GEP encoding is prerequisite for certifiABILITY, not
     just precision — a sharper form of the #31 verdict.

Ablation + certificate together, the paper statement: user-copied
bytes are REMOVABLE from the call-graph derivation (ablation, exact)
and their apparent reach in the closure is an artifact of the
field-insensitivity quotient (certificate, 62/62 absorbed) — the
separation theorem holds at the answer level, and naming the residual
crossing set is exactly the field-sensitivity frontier.

### Trace-payload sink model SHIPPED: --cfl-sink-instr + read-back contract confirmer (task #32, 2026-08-01)

The reviewed SINK family from the task #31 design conclusion is now an
implemented, contract-gated model — the first of the #31/#32 channel
models to graduate from ablation preview to shipped flag.

--cfl-confirm-sinks (measurement, standalone): machine-checks the
read-back contract at every payload accessor callsite
(ring_buffer_event_data, perf_trace_buf_alloc). The returned pointer
is walked as PTR (GEP/cast/phi chains); loads yield VAL (payload
content) walked through casts/arithmetic, with inttoptr(VAL)
laundering re-entering as PTR. Called-operand use = VIOLATION;
leaving the local walk = named ESCAPE; GEP-index/branch-condition use
is benign BY THE THEOREM (data-indexed selection: the certified
control channel, soundly over-approximated). Explicit walk cap
escapes, never silent.

--cfl-sink-instr (the model): seals cluster joins at the M4
trace-payload cell family {ring_buffer_, trace_buf} — stores keep
their own cell, joins to stored objects' keys are suppressed.
Auto-runs the confirmer and REFUSES (hard error) on any VIOLATION.
Lockdep sealing deliberately deferred: production kernels drop
CONFIG_LOCKDEP entirely, and its -110-answer M3 signature deserves
its own compare-only contract before sealing.

km verdict (kernel/-only subset, both runs current binary):

  contract: 171 accessor sites = 21 CONFIRMED / 150 ESCAPE /
    0 VIOLATION. The escape histogram is the review inventory, and it
    tells one story: 127/150 are perf_trace_run_bpf_submit — the
    payload handed to BPF programs as the ctx ARGUMENT (the
    already-certified BPF crossing family: kernel FRESH code pointer,
    payload-determined contents), never as a called operand. The rest:
    strcpy/strscpy (27, payload as dest = write-into-sink, not
    intrinsic so not auto-benign), filter/discard predicates (10,
    compare-only by design), fetch/print helpers, 2 ptr-stores
    (fbuffer->entry / iter->ent), 3 indirect-arg, 2 memcpy-out.
  answers: 92,874 vs 95,318 baseline pairs = -2,444 / +0 — pure
    removals, the M4/M5 smear family (relay_buf_fault,
    perf_mmap_fault, generic_delete_inode, ... the laundered fn-pool
    targets). 22.4M joins sealed (final iteration; M4 measured 35.6M
    under the ops-pairs config).

LEDGER-placement lesson RE-learned and now commented in the code:
probe/model reports in runFlowsToResolution must sit AFTER the
if (protOn) block — SinkAblate had been inside it since task #31 and
only ever printed because those runs carried --cfl-ops-pairs; both
sink prints now live at the unconditional site.

Kernel-scale identity run (canonical + --cfl-sink-instr, full bclist)
is the remaining acceptance gate before any canonical-config adoption
discussion.

### Kernel acceptance run: --cfl-sink-instr = -190,493/+0 (task #32, 2026-08-02)

Canonical config + --cfl-sink-instr, full bclist (4.25 h,
kernel-sinkinstr.log):

  contract: 726 payload accessor sites = 21 CONFIRMED / 705 ESCAPE /
    0 VIOLATION (escapes again dominated by perf_trace_run_bpf_submit
    — payload as BPF ctx argument, the certified crossing family).
  seal: 479,966,232 joins sealed at trace-payload cells.
  answers: 8,201,457 pairs vs the 8,391,950 pin = -190,493 / +0
    EXACTLY (both-directions comm; not even the nvme_sq flap fired).
    2.3% of the whole answer set was trace-payload smear: the
    laundered fn-pool families (alloc_pgt_page 4,744; acpi/rtc
    handlers 3,542 each; dmar_parse_* 1,655 each), concentrated in
    HOF/poll callers (__switchdev_handle_* 7,489 each,
    io_wq_worker_cancel, ring_buffer_poll_wait, n_tty_poll).

ZEROED-SITE INVENTORY (the adoption review): 63 of 7,842
pair-losing sites dropped to zero targets. Their lost targets are
diagnostic — filter_match_preds' pred->fn lost udp_sendmsg /
user_read / __traceiter_* (cross-subsystem junk, NOT the real
filter_pred_* family); __switchdev_handle_* lost vp_get_status /
dst_discard-class pool members. At all sampled zeroed sites the
pin's ENTIRE answer was the smear pool — no genuine callee was among
the removals, i.e. these sites never had a true witness and the pool
was masking under-resolution (pred->fn's registration path is a
separate, pre-existing modeling gap).

Caveats recorded for the adoption discussion: (1) classMatchesPats
is any-member on post-merge classes — a merged class containing one
ring_buffer_ value seals the whole class (merge contamination);
(2) sinkSealMemo staleness across merges cuts both ways in a shipped
model (probe-era "acceptable" note does not transfer). Both argue
for a write-provenance-keyed seal (only joins whose ORIGIN root is a
payload write) as the refinement if adoption stalls. Flag stays
opt-in; canonical pin unchanged.

### Task #32 CLOSED: stratum separation — census + probe + theorem, delivered (2026-08-02)

Scope shipped in full:
  CENSUS — strata bridge inventory (--cfl-census-strata: phys-bucket
    inttoptr/ptrtoint classification, 853 user-copy sites), writer-
    composition census, blob-formation diagnostic.
  PROBES — --cfl-probe-stratum-ablate (directmap/vmemmap/kernelmap),
    --cfl-probe-usercopy-ablate, --cfl-cert-usercopy,
    --cfl-confirm-sinks / --cfl-sink-instr.
  THEOREM, at full corpus scale, both content channels:
    (1) direct-map contents: -0/+0 byte-identical (severing all 834
        bridges changes nothing — redundant witness paths, not just
        silence);
    (2) user-copied bytes: -0/+59-flap (3 copy-body + 329 get_user
        closures severed; zero removals);
    (3) certified crossings NAMED: movable_ops through vmemmap
        METADATA (typed kernel objects — never sever), BPF programs
        receiving payload as ctx ARGUMENT (kernel FRESH code pointer,
        data-determined contents), GEP-index/branch = the benign
        data-indexed control channel, soundly over-approximated.
  Plus the shipped sink model (-190,493/+0 at kernel, opt-in).

Dispositions of the non-closed edges:
  - Nameable crossing INVENTORY (the certificate) is quotient-drowned
    at class granularity -> acceptance criterion of task #33 (field
    sensitivity), not an open item here.
  - --cfl-sink-instr canonical adoption: user decision "not yet";
    follow-on task = IR-anchored seal re-key + 63-site sweep.
  - Lockdep compare-only contract: deferred (CONFIG_LOCKDEP is off in
    production configs).

### Task #33 OPENED: field-keyed GEP — kernel campaign, not a fresh design (2026-08-02)

Corrected framing after re-reading §3.1: the encoding EXISTS and is
validated. The shift-indexed valley grammar (offsets mod prime P,
Dn/Up residue composition, VX wildcard absorption) is implemented in
flows-to as the per-shift fact planes (R/RB[class][shift], NSHIFT,
bridges = phase-2 pairwise VX with 1-bit provenance) — the same
machinery every #30-#32 instrument has been reading. Status verified
on current HEAD (2026-08-02): t_container 2/2 under fs13, libpng
fs13 per-icall identical to FI (27/9), harfbuzz fs13 = first sound
field-sensitive result (32m54s / 1.27 GB, 2,766 targets, strict
subset of FI's 2,795, 25/29 prunes source-verified correct).

What task #33 actually is — three fronts, in order:

1. THE SOUNDNESS BUG (blocker): harfbuzz would_match_input — fs13
   keeps only match_coverage of the ~7 match functions stored into
   the same ContextApplyFuncs match slot (gsubgpos.hh:2558/2751/
   2797/4041); FI resolves all; simple repros pass (t_ctxfuncs 4/4),
   145-function llvm-extract does NOT reproduce — a full-module
   interaction, unlocalized since 2026-07-08. Tools: --cfl-trace-func
   / --cfl-trace-fptr / --cfl-trace-value. Nothing kernel-scale can
   be trusted under fs until this is found.
2. KERNEL fs CAMPAIGN (the payoff): the canonical pin is FI; fs13
   has never run at km or kernel scale. Kernel C is the favorable
   case (wildcard density low — phase-2 bridges ~free; the C++
   container churn that made residue-copies net-negative is absent;
   --cfl-residue-copies re-evaluation rides along). Acceptance
   criteria fixed IN ADVANCE by #31/#32 findings:
     (a) the 1.1M-member pre-solve blob fragments (it is the
         field-insensitivity quotient — fs is the only lever that
         can split an exact equivalence);
     (b) the usercopy certificate becomes nameable (U classes stop
         merging into the giant; the 87% positive rate collapses
         toward a reviewable crossing list);
     (c) smear families sized by #30/#31 (kvm_x86_ops constexpr-GEP
         fields, tracepoint probe pools, ops-struct channels) shrink,
         measured as -N/+0-style per-icall diffs against the FI pin
         PLUS micro-suite exactness (t_ops, t_ops2, t_container,
         t_ctxfuncs) — answers WILL legitimately move, so acceptance
         is subset-plus-audit, not byte-identity.
3. COST CONTROL: DS0 adjacent-M coarsening (noted, empirically free
   so far), P selection (13 vs coarser), fx-fallback census at
   kernel scale (memcpy/ptrtoint/variable-GEP mix differs from C++),
   interaction with lazy mint / incremental / protection machinery
   that landed after the fs work (all built and tested FI-first).

Sequence: localize the bug (km-scale bisection of the harfbuzz
module set is the recorded next tool), then km fs13 A/B with the
acceptance trio, then full kernel.

### Task #33 framing CORRECTED against the task #27 record (2026-08-02)

The section above shipped with two stale claims; the Jul-24 record
(task #27) supersedes both, re-verified on HEAD today:

1. There is NO open fs soundness bug. would_match_input resolves all
   7 match functions under fs13; today's hb fs13 dump is
   byte-identical to FI (2,824 pairs both). Gone since the Jul 8-17
   incremental/bridge rework, diagnosed Jul 24.
2. "km fs13 A/B" has a recorded cost wall: 37.7 min for ONE drain
   (~200x FI, killed), wildcards dominated by ptrtoint-escape (3,467)
   + union-initializer (1,777); and hb discrimination is zero because
   fptr CLASSES merge before shift planes can discriminate (ensemble
   gluing: strings + variable-index arrays + memcpy'd tables).

What is genuinely NEW since that verdict, and what #33 actually
tests: the #31 blob verdict (post-dating #27) established that the
kernel giant is BORN PRE-SOLVE as the exact field-insensitivity
quotient — an ENCODING-level conflation, structurally different from
hb's in-solve cluster gluing, and touchable only by field-keyed
edges (f-edges are not a-edges: GEP cycles stop being V-equal
cycles by construction). Also new: the sink seal removes 27% of km
join traffic (joins were both the fs cost driver and a gluing
channel), and the #22/#23 int-provenance/asm modeling landed after
ptrtoint-escape was named the top wildcard source.

Decisive cheap experiment (in flight, km-fs13-blob.log): km fs13 +
--cfl-probe-blob-formation + --cfl-sink-instr. Reads out (a) whether
the born giant fragments under fs residues (pre-solve class sizes),
(b) whether the seal + current stack moves the 200x drain cost,
(c) answers if it converges. If (a) is yes and (b) is materially
better, the kernel fs campaign is on; if the giant fragments but
cost stays prohibitive, the next lever is fs-cost engineering
(wildcard-source reduction, P tuning) with the quotient argument as
justification; if the giant does NOT fragment, the blob is glued by
non-GEP channels even at the encoding level and per-field cells
demote to a precision-only tool behind identity work.

### VERDICT: km fs13 A/B under the seal — the born giant is NOT a constant-GEP quotient (task #33, 2026-08-02)

The pre-registered experiment (both legs: canonical + sink seal +
blob probe, kernel/-only subset, current HEAD):

                      FI+seal      fs13+seal
  giant (final)        71,140       64,211    (-9.7%)
  join events fed        106           29     (giant is ~all BORN)
  match-by-CFL         90,734       89,064    (-1,670)
  pairs                92,874       91,016    (-2,161/+303)
  CGPass                2.6 min     79.7 min  (31x)

READOUTS against the pre-committed branch logic:
  (a) FRAGMENTATION: NO. The quotient-fragmentation hypothesis is
      FALSIFIED at km — field residues on constant-offset GEPs shrink
      the born giant by only 9.7%. Corollary discovered en route: the
      sink seal alone already collapsed the FINAL giant from #31's
      177,574 to 71,140 with only ~100 join events feeding it — the
      in-solve gluing was largely the trace-payload channel, and what
      remains is the born quotient. That quotient's glue is the
      wildcard/laundering population, not constant GEPs: ptrtoint-
      escape (3,467 wildcard nodes), union initializers (1,777),
      variable-index GEPs — consistent with the #31 member census
      (mm walkers, BPF interpreter, load_module: int-arithmetic-heavy
      code). THE BLOB IS AN INT-ARITHMETIC QUOTIENT, NOT A GEP
      QUOTIENT.
  (b) COST: the wall moved 200x -> 31x (seal + a month of solver
      work), and fs13 now CONVERGES at km (79.7 min). Real but not
      decisive: 31x buys -1,670 match-CFL.
  (c) ANSWERS: -2,161/+303. Removals = RCU/perf pool smear
      (call_rcu_tasks* 123 each, perf IPI family) — plausibly correct
      prunes. The +303 ADDITIONS are the surprise: legitimate recall
      via the shift grammar's Up/Dn composition (member->container
      flows that FI's one-directional GEP 'a' edge cannot derive;
      exemplar __hrtimer_get_remaining -> ktime_get_*_fast_ns /
      trace_clock*, the hrtimer clock_base get_time slots). fs is not
      strictly tighter than FI — it is also SOUNDER on container
      walks, which matters for the soundness story independent of
      cost.

DISPOSITION per the branch: per-field cells demote to a
precision-plus-recall tool, not the blob lever. The sharpened
frontier is INT-PROVENANCE RESIDUES: the laundering channel
(ptrtoint -> add/sub const -> inttoptr) currently degrades to plain
'a' edges (or fx wildcards on escape), erasing offsets exactly where
the kernel does its pointer arithmetic; extending residue transforms
through constant int arithmetic would key the SAME mod-P planes
through the channel that actually glues the giant. That is new
encoding design (task #33 next front, needs design review), with the
+303 recall additions and the -1,670 prunes as the standing evidence
that the residue machinery itself works when offsets survive to it.

### Int-provenance residues FALSIFIED by census — the blob is irreducible at the offset abstraction (task #33, 2026-08-02)

--cfl-census-ptrtoint (km): classify every ptrtoint by the worst
thing its forward use-chains do. Verdict on 2,497 sites:

  ESCAPE 1,470 (58%)  stored/call-arg/returned — address-as-data
                      (snapshot_write_next, kprobe/traceprobe
                      registration, BPF trampolines, siginfo export)
  VARIABLE  341 (13%) non-constant strides (build_sched_domains,
                      rstat cursors, static_call table walks)
  OTHER     329 (13%) mul/shift/trunc/gep-index
  MASK      260 (10%) alignment/tag arithmetic
  CONST      32 (1%)  — 24 of them ONE __seccomp_filter +16384 idiom
  CMP        61 (2%), CONST0 0, DEAD 4

Wildcard-suppressible (CONST+CONST0+CMP+DEAD): 97/2,497 = 3%.

The "GEP in disguise" population does not exist at km scale. With
this, both offset-abstraction levers on the born giant are measured
dead: constant-GEP residues moved it -9.7%, and constant int-chain
residues have a 3% ceiling before touching a single hard case. The
giant's glue is loop-carried variable arithmetic and escaped
addresses — genuinely field-insensitive code whose conflation is
real at the offset abstraction, not an encoding artifact. No mod-P
(or any offset-keyed) refinement can split it.

TASK #33 DISPOSITION:
  - fs13 = a validated opt-in precision/recall instrument: -2,161
    smear / +303 genuine recall (Up/Dn container flows) at 31x cost,
    kernel-affordable-if-needed, converges. Not a default; not the
    blob lever.
  - The born giant is irreducible by offsets. Remaining candidate
    levers are IDENTITY-shaped, not offset-shaped — noting one
    specific stale verdict worth one cheap re-test: #17's
    "identity splitting REGRESSES" was measured PRE-SEAL, when the
    giant was 177k and join-glued; under the seal it is 71k and
    born, a different object. One km A/B re-run of the #17
    machinery under the seal would confirm or retire that verdict
    in its new context.
  - The usercopy-certificate certifiability goal inherits this:
    class-granular naming cannot come from offset refinement; the
    13% certified-clean floor stands as the honest number.

### Tagged-pointer rule + int-select/phi provenance fix + the teaching micro (task #33, 2026-08-02)

User direction: kernel code tags ALIGNED pointers in their low bits
(p|1 mark, p&~1 clear, v&7 extract) — (p|1)&~1 must equal p. Three
deliverables landed together:

1. TAG-ROUND-TRIP RULE (fs): a ptrtoint whose complete local
   use-closure is sub-alignment constant bit-ops + compares + tag
   extraction + inttoptr round trips no longer pays the fx escape
   wildcard — the plain a-edges (shift 0) are already the exact
   model. Any other use (store/call/ret, offset-destroying mask,
   variable or non-tag arithmetic, walk cap) keeps the wildcard: the
   source wildcard is the only sound cover for downstream rebasing
   through memory. Census reclassified accordingly: TAG 75 (3%) —
   rb_check_pages / rb_get_reader_page (the ring buffer's tagged
   reader page), rt_mutex_adjust_prio_chain, toggle_bp_slot; MASK
   260 -> 123; suppressible population 97 -> 203/2,497 (8%).

2. INT-SELECT/PHI PROVENANCE SOUNDNESS FIX, found by the micro:
   clang folds `flag ? (ulong)&a : (ulong)&b` into a select whose
   operands are ptrtoint CONSTANT EXPRESSIONS. visitSelectInst /
   visitPHINode early-returned on non-pointer types, AND
   getRepNodeForValue maps a ptrtoint CE to a special constant-pool
   node that silently absorbs flow — the whole chain dropped and the
   downstream icall resolved to NOTHING. Both visitors now use the
   atomic-handlers' laundering guards (ptr-width int +
   mayCarryPtrProvenance/mayBecomePointer), unwrap CE ptrtoints to
   their pointer operand, and apply the ptrtoint-escape wildcard
   discipline under fs (a CE never passes through visitPtrToIntInst,
   so this is its only wildcard site — tag-round-trip CEs are
   exempt). km A/B (canonical+seal): -0/+324 pure recall, dominated
   by tracing_stat_open (267). The KERNEL PIN WILL MOVE (+recall) on
   the next full run.

3. test/t_maskwalk.c — the explainable artifact. Three routes, one
   object pair each (sharing a pair cross-poisons routes through the
   (o,X)<->(o,s) bridges — the #27 ensemble effect in miniature):
     FI:    use_gep {fa1,fb1}  use_mask {fa2,fb2}  use_tag {fa3,fb3}
     fs13:  use_gep {fa1}      use_mask {fa2,fb2}  use_tag {fa3}
   gep: struct offsets survive value merging (fields pay). mask: the
   __va / page-align shape erases offsets BY DESIGN — irreducible
   under any offset-keyed refinement, both modes equal. tag: (p|1)&~1
   == p, exact under the new rule. Validation: smoke 4/4, libpng
   FI==fs13==27/9 unchanged.

### Sink-instr re-key FALSIFIES the seal: the -190k was join-denial, not payload semantics (task #34, 2026-08-02)

The adoption question ("re-key the name-matched seal to IR anchors,
then decide default") answered itself by falsifying the seal. Three
implementations, one km A/B each (base = canonical, 95,640 pairs,
carries the select/phi fix; name-keyed reference = -2,442/+0):

- v1, anchor the confirmer's payload-pointer chain values and seal
  cellsOf[find(class)]: -59,737/+0, 195M joins sealed (9x the
  name-keyed 22M). Removals at clocksource_watchdog, handle_edge_irq,
  bpf_link_*, smp_call_function_many_cond — presolve copy chains merge
  the accessor's void* results into generic-pointer classes, so the
  class's cell list is mostly FOREIGN deref sites. Name-keyed removals
  were a strict subset; scope semantically wrong.
- v2, seal only each anchor's own deref node: 673 anchors collapse to
  3 presolve cell classes, 666k joins sealed, -0/+0. The name-keyed
  -2,442 is entirely missed: the glue forms at the rb-page OBJECT
  cells reached through ring-buffer-internal pointers, and facts flow
  around the sealed accessor-boundary cells. The name patterns had
  been OBJECT-keyed all along — that emergent scope, not the payload
  boundary, is what the seal's effect lived in.
- v3, the semantically honest model, SHIPPED in-tree: OPAQUE ARENA at
  the accessor boundary. visitCallBase binds the return of each
  payload accessor (ring_buffer_event_data, perf_trace_buf_alloc —
  the same two names the contract confirmer keys on) to ONE shared
  opaque object per accessor; args still feed the real body; ret
  binding into ring-buffer internals is replaced. Payload write->read
  flow is PRESERVED (the seal cut it — the arena is strictly sounder),
  only the unification of payload cells with kernel-object cells never
  forms. No join-time check, no name patterns, no sealCell machinery
  (all deleted). Result: 171 accessor callsites bound, contract
  21/150/0 — and -0/+0 EXACT.

VERDICT — reinterpretation of the #32 kernel acceptance number:
- The true trace-payload channel contributes ZERO false icall pairs
  at km. All 171 accessor sites live under kernel/, so the payload
  semantics are FULLY CONTAINED in the km subset: the kernel-scale
  -190,493 cannot have been payload precision either.
- What the name-keyed seal actually did: deny 22M+ joins at cells
  whose merged classes happened to contain a payload-named value —
  emergent-scope glue denial, a cousin of the ablation probes. Its
  removed pairs (703 targets scattered over 211 sites: trace_clock*,
  buffer_pipe_buf_*, perf_mmap_* mixed with generic_delete_inode,
  alarmtimer_rtc_add_device) are giant-membership subtractions. The
  63 zeroed-site inventory ("masked under-resolution") was the same
  symptom seen from the other side.
- ADOPTION: the name-keyed seal is RETIRED — its win is unprincipled
  and its removals were never validated as false pairs (the contract
  only certifies accessor-derived dispatch, not the emergent scope).
  --cfl-sink-instr now IS the arena model: sound, contract-gated,
  ~free, and worth +/-0 at km — kept as the honest instrument, no
  case for default. The user's "not yet" call was right.
- The 63-site sweep is MOOT in its original form (it audited seal
  zeroings; the arena zeroes nothing). Falsification count for the
  paper spine: this is #6, and the second time a headline win
  dissolved under an intrinsic re-key (cf. #17 identity splitting).

Validation: smoke 4/4, t_maskwalk FI 6/6 unchanged. Next: kernel
canonical re-pin run carrying the select/phi provenance fix (+324
recall at km) and the tag rule — no sink flag in the canonical config.

### Kernel identity run: pin does NOT move — select/phi fix is kernel-redundant (2026-08-02)

Canonical config, full bclist, carrying the select/phi provenance fix,
the tag rule (inert at NB=0) and the arena code (inert without the
flag). Result: BYTE-IDENTICAL to the kernel-gepfix pin — -0/+0 over
all 8,391,950 dump lines (LC_ALL=C both-directions comm; note the pin
.gz needed a C-locale re-sort — the locale trap again). No nvme_sq
flap. 4.43 h vs the pin's 4.12 h (+7.5% from the modeled int-prov
mass: 19,750 int stores + 27,926 loads witnessed, 4-5x the km counts).

- The predicted pin move (+324-recall class from km) is FALSIFIED at
  full scale: tracing_stat_open sits at 2,355 pairs in BOTH runs — the
  chain the fix recovers at km already has redundant witnesses in the
  full-kernel graph (other TUs' paths into the same stat machinery)
  and is quotient-drowned besides. Same redundancy pattern as the
  directmap ablation: per-TU-visible soundness gaps often carry
  redundant witnesses at full scale. The fix STAYS (km proves real
  dropped chains; kernel redundancy is corpus luck, not a guarantee).
- OPERATIONAL: the first attempt OOM'd at the default --mem-limit=80
  (49 GB) — died at presolve-saturation iteration 62/62. The limit is
  RLIMIT_AS (address space), not RSS: peak RSS was only ~44 GB but VSZ
  crossed 49 GB. Canonical kernel runs now need --mem-limit=92 on the
  62 GB box. Module loading alone reaches ~44 GB RSS in the first few
  minutes; the envelope statement becomes "4.4 h, <45 GB RSS /
  ~55 GB AS".

### Tracepoint keyed channels: census + model + km validation (task #35, 2026-08-02)

The identity-shaped frontier, sized from the pin: 964 __traceiter_*
callers carry 1,504,648 pairs = 17.9% of the 8.39M kernel answer set
(~1,561 targets/site). Rodata (task #25) was re-measured on the way —
--cfl-probe-rodata-joins over-removal bound = -29,128/+0 at km (30%),
NOT closable, upgraded and queued behind this.

CENSUS (--cfl-census-tracepoint, km + kernel): the registration family
(tracepoint_probe_register/_prio/_prio_may_exist/_unregister) has 87
callsites kernel-wide: 81 CONST (@__tracepoint_* argument, all with
static probe too) + 6 LOAD, and the LOAD sites are exactly two
struct-mediated registrars — trace_event_reg (x4: ftrace/perf paths;
pairs live in trace_event_call -> trace_event_class static
initializers) and bpf_probe_register/unregister (pairs live in
bpf_raw_event_map {tp, __bpf_trace_*}). Zero FORMAL/OTHER. All 964
__traceiter bodies name their key global at the funcs-head load
(constexpr GEP), zero keyless. 100% classification — the model needs
no unsound fallback.

MODEL (--cfl-tracepoint-keys): per-key channel cells fnCell =
deref(@__tracepoint_X), dataCell = deref(fnCell). Every register-
family callsite is severed from the generic body — the body's shared
tp formal IS the pooling channel — with CONST sites binding
probe/data directly, walker pairs covering the two mediators, and
mediator data pooled into walker keys' data cells (data was globally
pooled before; only the fn plane gains keying). Each __traceiter icall
reads its own key's cells, and the iterator's funcs-head load is
severed (the channel replaces it; sound because the completeness
counters — unclassified sites, keyless iterators, unmapped keys — are
all zero and LOUD). Cluster joins key on POINTER origins, so per-key
fn channels cannot merge even when DECLARE_EVENT_CLASS templates share
probe fns across events.

km VALIDATION (v1, cell channel): 37 const binds + 812 walker pairs
over 194 keys, all completeness counters 0, and the A/B vs base is
-0/+0 EXACT — with every registration severed and the funcs path cut,
the channel ALONE reproduces the baseline resolution byte-for-byte.
Crucially the km baseline was ALREADY per-key exact
(__traceiter_sched_switch: 11 targets, all sched_switch probes) — the
1,561/site pooling is a KERNEL-SCALE phenomenon (the 1.1M-member
giant absorbs the funcs cells; the 177k km giant does not).

KERNEL A/B of v1: -0/+59-flap — BYTE-IDENTICAL pooling (median 686
targets/site, max 4,616 at the x86_fpu family, all unchanged). The
channel CONTENT was exact but the channel CELL was quotient-
contaminated: deref(@__tracepoint_X) sits inside the kernel giant (tp
pointers travel the __tracepoint_ptrs section arrays and iterator
formals, merging every tp's cells), so the dispatch edge read the
whole quotient back in. The #30 store-hub wall, rediscovered: keyed
discrimination is absorbed the moment the key's CELL is merged.

v2: junctions, not cells. Per-key synthetic value nodes J_X/D_X
(createValueNode(nullptr)) carry probe -> J_X -> called-operand and
data -> D_X -> arg0 as plain a-edges. Junctions are referenced by
nothing but the model's own edges — no cell join can absorb them.
km A/B: -1,434/+0, all NON-traceiter smear (the tracepoint machinery's
heap arrays had been leaking into other icall resolutions; v1's cell
writes masked this). But kernel A/B v2 = BYTE-IDENTICAL AGAIN, and
--cfl-trace-fptr told the whole story: the fpu operand's class is a
solve-time merged mega-class (handle_edge_irq irq_chip loads, other
__traceiter fptr loads, balance_callback int-provenance chains), and
its in-edges come from the class displaying as perf_trace_task_newtask
— i.e. THE PROBE FUNCTIONS' OWN VALUE CLASSES ARE INSIDE THE GIANT.
Fn identity is a casualty of the V-merge quotient: any graph channel
sourced from fn value nodes imports the pool at the SOURCE, and any
edge into the operand lands in a giant-merged class at the SINK. A
further correction: the "pooled" sites were never CFL-resolved at all
— their dump entries are the TYPE-BASED FALLBACK (alphabetical
type-compatible sets; km baseline was pooled too at ~523/site, and
sched_switch's exact 11 was the exception, not the rule).

v3 (SHIPPED): ANSWER-LEVEL PRIMITIVE — the #14 static_call precedent.
The resolution loop takes targets for __traceiter sites directly from
the census-complete binding table (key -> registered probes +
defensive __probestub_X), skipping the R[operand-class] scan; Callees
insertion and callee-flow wiring proceed unchanged, so probe formals
still receive their actuals. Graph edges kept: data junction + the
severs; fn junction dropped (it could only import the giant). Keys
with any non-static probe registration fall back to the graph path,
counted LOUDLY (zero today). Two walker bugs found by the
type-rejection counter: @llvm.used matched the "initializer references
a tracepoint" scan and bound ALL of a TU's probes to one key (fixed:
only trace_event_call-typed globals and __bpf_raw_tp_map-section
globals may bind), and bpf maps are union-wrapped so the type name is
invisible (fixed: section anchor).

km VERDICT (final): -40,965/+0 EXACT — 42.8% of the km answer set,
removals only. 194/194 keys bound (37 const + 558 walker pairs), 0
type rejections, all completeness counters 0. Traceiter sites: ~523
pooled -> ~4-9 exact registered probes (sched_switch: 8 probes +
stub; the baseline's __SCT__/iterator-self entries are gone — the
funcs-array dispatch never calls them). Non-traceiter removals = the
known smear channel (bpf_seq_read 679, cgroup_file_write 76...).
Smoke 4/4 flag-off. Kernel A/B next.

DESIGN PRINCIPLE (paper): identity-keyed dispatch channels cannot be
carried by the graph once the quotient has merged either endpoint —
and at kernel scale it merges BOTH (fn identities at the source,
operand classes at the sink). Channels must live at the ANSWER level
(modeled primitives over census-complete inventories, #14/#35) until
the solver grows provenance cells (#30 frontier) that exempt fn
identity from V-merging.

### KERNEL VERDICT: -1,503,226/+0 — 17.9% of the answer set, and 19% faster (task #35, 2026-08-03)

Canonical config + --cfl-tracepoint-keys, full bclist, 3.33 h
(vs the pin's 4.12 h — severing the tracepoint registration machinery
from the solve cut runtime ~19%; kernel-tpkeys3.log). Both-directions
LC_ALL=C comm vs the kernel-gepfix pin:

- REMOVED 1,503,226 / ADDED 0 (no nvme flap). 8,391,950 -> 6,888,724.
- __traceiter pairs: 1,504,648 -> 3,871 (964 sites x ~4). Exemplar
  __traceiter_x86_fpu_init_state: 4,616 type-fallback pairs -> exactly
  {trace_event_raw_event_x86_fpu, perf_trace_x86_fpu,
  __bpf_trace_x86_fpu, __probestub_x86_fpu_init_state}.
- Non-traceiter removals: 2,449, ALL at __gen8_ppgtt_foreach (i915,
  a giant member shedding tracepoint-glued smear).
- Completeness certificate at kernel scale: 964/964 keys bound (39
  const + 2,868 walker pairs), 0 type rejections, 0 unclassified reg
  sites, 0 keyless iterators, 0 unmapped keys, 0 dyn-probe fallbacks.

This is the largest single precision movement in the project (prior
best: INVOKE pipeline -3.5%). Character differs from the retired seal:
the inventory is census-complete and structural (registration API +
static initializers), the km channel reproduced ground-truth
resolution exactly before the primitive was added, every deviation
path is counted loudly, and the direction is removals-only with the
removed entries being TYPE-FALLBACK pairs (sites CFL never resolved),
not CFL answers. Adoption (default-on vs opt-in) = user's call; the
flag is opt-in until then and the canonical pin is unchanged.

Follow-on candidates with the same answer-level shape: the singleton
ops-struct families (kvm_x86_ops / x86_pmu: vcpu_run 134k + enter_smm
49k pairs), and #25 rodata copy-not-unify (-29,128/+0 km bound).

### static_call ops-table channel: -1,197,091/+29 at kernel scale (task #36, 2026-08-03)

The follow-on landed the same day (df07d7f). Re-sized prize: the
__SCT__ static_call families carry 1,225,715 pin pairs (kvm_x86
1,034,082 + x86_pmu 132,400 + apic_call 51,918 + tails), and they are
TYPE-FALLBACK: static_call_update's fn argument is a dynamic
ops-struct load the graph never resolves, so every vcpu_run __SCT__
site carried the 4,928-fn type-compatible set.

MODEL (--cfl-static-ops-tables, requires --cfl-static-call): at each
const-key __static_call_update site, classify the fn source —
  - constant fn: direct table entry (cond_resched family lands here);
  - load gep(%struct.X, base, 0, N), or the SINGLETON shapes (no-gep
    field-0 load of @kvm_pmu_ops; canonical i8 byte-geps mapped
    offset->field via DataLayout StructLayout): a pending, resolved
    against EVERY same-typed global initializer (vmx/svm kvm_x86_ops,
    intel/amd pmu, the apic drivers; suffix-canonicalized type names);
  - select/phi composed for OPTIONAL_RET0's `load ?: return0`;
  - anything else UNTABLES the key loudly (kernel: 3 keys, led by
    bpf_dispatcher's JIT image — graph behavior is correct there).
Tabled __SCT__ sites take targets from the table in the resolution
loop (#35 ownership pattern). The table is AUTHORITATIVE over
isCompatible: __static_call_return0 (long(void)) is a real runtime
target at typed RET0 sites — mismatches are warned and KEPT, never
filtered (90 at kernel scale, all return0).

KERNEL VERDICT: -1,197,091 / +88 vs the pin (14.3% of the answer
set), 3.89 h. The 88 additions: 59 = the known nvme_sq flap, 18 =
__static_call_return0 recall, 11 = default_send_IPI_*_phys apic-table
recall — every non-flap addition is a REAL target the type fallback
missed. 188 keys tabled (59 const + 171 load-shaped), 10,785 sites
model-answered, 150 sites kept graph behavior under the 3 untabled
keys. Repro-subset validation (km + arch/x86/kvm + arch/x86/events):
-204,758/+18; get_rflags -> {vmx,svm}, pmu_hw_event_available ->
{intel,amd}, cache_reg 131 sites x 3 exact; no fat SCT set remains.

COMBINED PICTURE: #35 (-1,503,226) + #36 (-1,197,091) ≈ -2.70M pairs
= 32% of the 8.39M pin, from two census-complete answer-level
primitives, both with faster runs than baseline. Both flags opt-in;
adoption/default = user's call (a combined-flag kernel run would be
the natural new-pin candidate if adopted).

### Rodata copy-not-unify: the honest model is answer-neutral — probe bound falsified (task #25 CLOSED, 2026-08-03)

The sound implementation cost ~40 lines: the #30 provenance-protection
machinery IS copy-not-unify (writer joins merge, reader joins attach
via non-transitive bridges, mixed cells demote), so --cfl-rodata-copy
just protects every rodata origin (rootRodata was already minted, both
initially and mid-fixpoint) and extends protOn. Validation: t_ops /
t_ops2 / t_container / t_allocinit exact with the flag on (const ops
tables still resolve — initializer flow preserved), smoke 4/4.

km VERDICT: -0/+0 EXACT, runtime unchanged. The machinery engaged
fully — 3,570 rodata origins protected, 3,403 writer merges, 2,720
reader bridges, 82 demotions — and no answer moved. The probe's
-29,128/+0 (30% of km) is therefore a JOIN-DENIAL ARTIFACT, the third
instance of the emergent-scope pattern (trace-payload seal, tracepoint
cell channel): the probe removed pairs by denying WRITER-shaped joins
at rodata-witnessed cells — stores through mixed-pointee pointers and
memcpy chains, flows that are semantically real — while the honest
model cuts only reader-reader unification, which is answer-neutral.
"String-literal witnesses seed the hub" (the #26-era diagnosis) is
DEAD as a precision lever: the glue rides written-through cells, not
pure-const readership.

DISPOSITION: #25 CLOSED. --cfl-rodata-copy stays in-tree as a sound,
neutral, off-by-default instrument. The pin-candidate combination
(user directive) proceeds with the TWO positive levers:
--cfl-tracepoint-keys + --cfl-static-ops-tables.

### PIN CANDIDATE: canonical + tpkeys + static-ops-tables = -2,700,317/+29, 2.98 h (2026-08-03)

Per user directive (rodata was the third lever; its honest model came
back answer-neutral, so the candidate combines the two positive ones).
Full stats + completeness certificates:
test/baselines/kernel-pincand-stats.txt; answer set (sha256-pinned)
in ~/fast/ka-scratch/baselines/kernel-pincand-icalls.sort.gz.

Headline: 18,189 icalls / 5,691,662 dump lines — 32.2% below the
kernel-gepfix pin — in 2.98 h (-28% runtime; the two severed
machineries also cut solve cost). Additions are 29 REAL-RECALL pairs
(return0 + apic IPI table entries the type fallback missed); no nvme
flap this run. The removal set decomposes exactly as
solo-#35 ∪ solo-#36 + 45,453 synergy pairs at kvm dispatch bodies,
with union-only = 0 (combination loses nothing either solo run
removed). ADOPTION = user sign-off; until then kernel-gepfix remains
canonical.

### ADOPTED: identity channels are the canonical config; pin = kernel-idchan (2026-08-03)

User adoption: --cfl-tracepoint-keys and --cfl-static-ops-tables are
DEFAULT ON (opt out with =false). Outside the monolithic flows-to
mode they auto-disable unless explicitly requested (their graph-build
severs are only sound paired with the answer-level resolution loop);
--cfl-static-ops-tables also auto-disables if --cfl-static-call=false
was chosen. CANONICAL PIN is now kernel-idchan
(test/baselines/kernel-idchan-stats.txt): 18,189 icalls / 5,691,662
dump lines, 2.98 h, superseding kernel-gepfix. The rodata copy-not-
unify flag stays default OFF (answer-neutral instrument).

### Fat-site census verdict: the remaining mass is ONE fish (task #37, 2026-08-03)

--cfl-census-icall-shape at kernel scale (defaults on, kernel-idchan
config): 6,138 fat sites (>=100 targets) carry 5,306,253 pairs = 93%
of the remaining 5.69M answer set, spread over 2,231 IR-shape
families — and effectively EVERY fat site sits on the SAME operand
class: the giant (1,139,703 members, 204,293 fact roots). The fat
answers are all R[giant] ∩ type-compatible, seen from different IR
angles.

Family structure (top-40 = 3.47M pairs):
- shapeless ~2.73M: double-indirect loads (1.03M/406 sites), untyped
  byte-gep loads (1.10M across 2level/parambase/plain), *param loads
  (256k), phi/select (169k) — no per-family inventory exists; these
  are the quotient itself.
- named struct.field ~522k in the top-40 (+ most of the 1.83M
  long-tail): intel_context_ops.14, hrtimer_clock_base.6,
  percpu_ref_data.1, bpf_prog.9, virtio_config_ops.7, sk_buff
  destructor fields, regmap.1/2... each 10-25k, hundreds of them.
- formal (fn,data) channels ~217k: decompressor flush/error params
  (unlzo#6 ...), call_timer_fn#1, smp_call_function_many_cond#1.

CONSEQUENCE: there is no third #35/#36-style campaign — no single
family is worth >110k pairs, and the shapeless majority has no
census-complete inventory by construction. The remaining lever set:
(A) provenance-cells solver redesign (fn identity exempt from
    V-merging, the #30 frontier): deflates ALL 6,138 sites at once —
    the one true big fish, research-grade effort, now cleanly sized
    at ~5.3M pairs / 93% of the answer set;
(B) generic field-keyed tables (the #36 mechanism generalized to
    non-singleton ops structs + store-side inventories per #29):
    covers the named-field + formal slices (~0.7-2.3M depending on
    tail composition), engineering-grade, but leans toward
    type+field-flavored resolution and needs store-escape
    completeness arguments per family class;
(C) stop: declare the quotient boundary — 18,189 icalls at a median
    well under 100 targets, with the fat tail documented as the
    field-insensitive quotient's residue.

### Giant anatomy forensics: fact smearing, not class merging — and the fn-provenance-plane design (task #38, 2026-08-03)

Three measurements (km, kernel-idchan defaults) close the "what leads
to the giant quotient" question:

1. CLASS MERGING IS INNOCENT: 0 of 4,733 address-taken fn classes are
   union-find-merged into the giant. The sound merge-exemption lever
   has nothing to exempt.
2. THE MECHANISM IS FACT ACCUMULATION: R[giant] holds 25,884 roots of
   which 2,404 are fn roots, visible to every reader of any of the
   cluster's 141,040 member cells. Exemplar trace (acct_pin_kill,
   absurd target at clocksource_resume): the fn has ONE a-edge — its
   legitimate store into the fs_pin cell — and that entry cell's class
   is already giant-merged; one hop in, 5,900 propagation events out.
3. ENTRY IS DIFFUSE: 3,456 of 6,308 fn out-a edges land in the giant
   through 1,389 DISTINCT entry classes (top entry: 83 fns; top-30
   cover <20%). Every callback-registration cell is its own door.
   Targeted channel guards cannot cover this; the injection must be
   structural.

DESIGN BRIEF — FN-PROVENANCE PLANES (the scoped form of provenance
cells this evidence supports):
- Observation: ANSWERS depend only on fn-root facts — 2,404 of 25,884
  roots (9%) at km. The expensive treatment can be restricted to the
  fn plane; every other origin keeps the cheap transitive quotient.
- Property to enforce: cluster-join fact visibility for FN facts must
  be WITNESS-SCOPED, not cluster-wide. A reader cell sees a fn fact
  only if a join-witness chain (shared (origin, shift) evidence)
  connects it to the fact's ENTRY cell — the #30 reader-bridge
  (copy-out, non-transitive) semantics, generalized from protected
  origins to the fn plane of every join, with the K-collapse
  self-limiting rule inherited to bound plane copies (the #30 kernel
  OOM lesson).
- Sketch: fn bits leave the merged R planes; they live in per-entry-
  cell side tables plus a recorded join-witness graph; icall
  resolution does a demand-driven witness-closure readback from the
  fptr class (18k icalls — readback is cheap; the witness graph is
  the new memory cost).
- Prize: the 5.3M-pair / 93% giant residue, all 6,138 fat sites at
  once. Risks: witness-closure semantics must reproduce the V/VX
  shift-matching rules exactly (Lean-checkable like sderiv_catchup);
  join-witness recording is on the hot path; cost model unproven.

This is a solver-core rework (days, not an A/B afternoon) — design
sign-off is the next gate.

### Phase-1 over-unification: exposed, measured, and a free lever shipped (task #38, 2026-08-04)

The user's "is there a hub in phase 1?" question broke the born-giant
story open. --cfl-probe-born-hub found NO hub — because the 41,350-
member born component's true mutual-flow core is 41 NODES. The
grammar explains it: V := (M? -a)* M? (a M?)* is the SYMMETRIC
may-alias relation; computeVSCC over a symmetric relation returns
alias-CONNECTED COMPONENTS, and the presolve merges them — treating
non-transitive alias as transitive. The born giant is Steensgaard-
style over-unification, a scale policy, NOT the exact FI quotient
(#31's "born = exact, unsplittable" is refuted; the exact quotient is
41 nodes).

Two sound-by-construction experiments (unmerging cannot lose flows):
- --cfl-presolve-exact (merge only provable value-equalities: 4,915
  merges, largest SCC 96, 61 ms, GraCFL presolve skipped entirely):
  km -2,710/+0 REMOVALS-ONLY — the (fn,data) formal fat sites deflate
  (smp_call_function_many_cond, execute_in_process_context,
  stop_machine_cpuslocked, opt_pre_handler) — at 9.2x runtime.
- --cfl-presolve-cone (hybrid: keep the component quotient for the
  data plane; exclude only the backward value-flow cone of icall
  called operands): km 2,442/145,068 nodes = 1.7% cone, -1,184/+0 at
  BASELINE cost (112 s vs 111 s). KERNEL: 22,973/1,031,125 = 2.2%
  cone, -201,724/+0 vs the kernel-idchan pin (3.5% of the answer
  set), 3.07 h vs 2.98 h (+3%). Removals spread wide-and-shallow over
  4,265 callers: switchdev handler walkers (7,489 x3), percpu_ref,
  smp_call, i915 fences, drm actions, decompressors.

Known residue and the ladder above the cone: the cone walks static
a-edges only, so smears that cross CELL-ALIAS joins stay (km gap to
full exact: 1,526 pairs; the kernel giant is mostly in-solve-grown,
so the larger share of the 5.3M residue is phase-2 joins, not
phase-1 welds). Next rungs, in order of ambition: bidi-partition cone
extension (cross may-alias cell partitions during the cone walk);
in-solve join-side cone exemption (the same answer-relevance
discipline applied to cluster joins); fn-provenance planes (the full
witness-scoped visibility redesign, brief pinned earlier).

ADOPTION QUESTION: --cfl-presolve-cone is free (+3%), sound-direction
only, and orthogonal to the adopted identity channels. Default-on
candidate = user's call.

### Rung 2 null result: reader-side discipline cannot reach writer-side coupling (task #38, 2026-08-04)

--cfl-join-cone (every origin protection-eligible; answer-cone cells
bridge as prot readers, everything else merges as today): km -0/+0
EXACT vs the cone baseline, runtime unchanged. The ledger says why —
only 418 reader bridges fired across the whole solve: answer-cone
cells virtually never reach a join as PURE readers, because their
classes are in-edged (fptr-chain deref cells receive real stores, and
class-folded hasIn marks the rest). Writers must merge — store
visibility is semantic — so the reader/writer discipline never
engages where the coupling actually happens.

DIAGNOSIS, and the narrowed design space: phase-2 giant coupling is
WRITER-SIDE. A written cell keyed (o1) that joins a cluster via o1
carries its o2/o3/... planes along, because the merge unions ALL
planes; the semantic requirement was only the SHARED origin's plane,
both ways. Preventing writer-side smear requires per-origin plane
exchange at joins — facts crossing per shared origin with classes
kept separate — which is exactly the pairwise storage the #18 merge
layer replaced for scale, and exactly the fn-provenance-plane brief
(witness-scoped visibility). Rung 2 has no cheap form; the ladder
collapses to rung 3 with a bounded variant now well-motivated:
per-plane exchange ONLY at answer-cone cells (2% of nodes), reader
AND writer, fn plane only — pairwise cost bounded by cone size.

### Modularity thesis confirmed at kernel scale: the object plane is bimodal (task #38, 2026-08-04)

--cfl-census-couplers, full bclist. The user's thesis — the kernel is
naturally compartmentalized at the data-object level, and the giant
is shared-plumbing artifact — holds in the strongest form the data
could take:

- BIMODAL, EMPTY MIDDLE, at both scales. Kernel icall-operand data-
  subsystem diversity: [0]=1,638 [1]=602 [2]=266 [3]=2 [4..7]=0
  [8+]=16,141. (km: 455 vs 0 vs 1,081.) A dispatch site either sees
  <=2 subsystems' objects or ~all of them; compartmentalization is
  the natural state and the giant is a phase transition.
- WELDS ARE RARE: kernel 1,695 / 173,527 merges (0.98%; km 2.6%).
- WELDER TAXONOMY (three classes, from the blame table):
  1. UNIVERSAL COURIERS, catastrophic and few: mptcp_stream_accept
     (54 subsystems in one weld — the socket layer is the kernel's
     universal object courier), __warn (55 — diagnostics touch
     everything), bpf tp maps / iterators, kthread/stopper engines,
     procfs show iterators (km: perf_ctx_sched_task_cb at 55).
  2. HONEST NEIGHBORS, small and semantically correct: ext4<->jbd2
     journal buffers (x6+x4+x4+x4 at 2 subsystems), quota transfer,
     snd_hda — real shared objects between adjacent subsystems, as
     they should be.
  3. THE ALLOCATOR: kmalloc_caches (6 subsystems) — the known heap-
     identity story (#17), now placed in context.
- Census caveat: the 64-bit subsystem mask saturates (63 named + 1
  overflow slot) at kernel scale; drivers'/fs' long tail pools into
  the overflow bit, so courier diversities are lower bounds and a
  wider-mask rerun would sharpen fs/X-vs-fs/Y specifics.

ROADMAP IMPLICATION (inverts the rung-3-first plan): summarize/model
the class-1 courier list — each is a #35/#36-shaped campaign with a
nameable inventory (socket accept/skb paths, warn/diagnostics, bpf
iterator engines, kthread/stopper (fn,data) channels, procfs
iterators) — and the object plane fragments into subsystem cones
without solver surgery. Class-2 stays (correct), class-3 is heap
identity (revisit #17 under the post-idchan graph). Rung-3 plane
exchange is reserved for the residue after the courier campaigns.

## Task #39: surgical nexus field sensitivity — --cfl-nexus-fields (2026-08-04)

Class-B remedy from the #38 nexus discovery, built class-B-first per the
dependency the user identified: container heads (`task->children`,
`tsk->ptraced`) live at fixed offsets INSIDE the fat objects, so class-A
container summaries have nothing to key on until the fat-object cell is
split — class B gives class A its keys.

**Design.** The fs13 shift machinery unchanged, but exact residue minting
is gated: only origins of listed nexus struct types mint at shift 0;
every other root — including FUNCTION roots — mints directly on the
wildcard plane. Wildcard minting is bit-identical to FI for that origin
(one `(o,X)` join cluster, no exact keys, no VX bridges), so the residue
cost is confined to the nexus population. Typing: globals/allocas by
value type; heap sites by use (classes of stripped bases of GEPs whose
source element type is nexus, plus a backward a-edge closure that
crosses cells on purpose to reach fork-side alloc callsites).
Over-marking costs planes, never soundness.

**km results (default list task_struct,file,cred,signal_struct,device,module):**
- **-1,846/+0**, a STRICT SUBSET of full fs13's -4,499/+0 — 41% of the
  precision for 22% of the cost. Removal profile: callback-carrier
  dispatch (execute_in_process_context 454, smp_call_function_many_cond
  442, stop_machine 132, async_schedule 134) separated by
  task_struct/signal_struct cell splits.
- **Fn-roots-at-X is free**: byte-identical answers, 25.5min → 17.5min.
  A fn identity's shift never keys anything answer-relevant (answers
  union the X plane; rotation is absorbing at X; `(fn,X)` join keys are
  FI-identical), while exact fn facts blanket the graph and spread
  across every plane at each f-edge rotation.
- **212 exact-minted roots carry the entire effect** (of 46,869 rids).
- **Widened-list null**: +14 types (bpf_link, trace_array, irq_desc,
  work_struct, timer_list, ...) bought only +29 more removals. The
  fs13-only gap (bpf_link_release 508, tracing_stat_open 267, ...) is
  EMBEDDED-TYPE origins: `bpf_link` lives inside `bpf_tracing_link`,
  and name-matched GEP typing misses the containing type. Containment
  closure would recover them, but for promiscuous carriers
  (`work_struct` embeds in hundreds of types) it approaches full fs13.

**Cost structure nailed.** 9.4× residual cost for 212 exact origins:
exact planes are FULL-UNIVERSE FactSet bitsets (46,869 bits) though
they can only ever contain the ≤212 nexus rids — ~220× width waste per
occupied plane, and occupied-plane count × universe width is exactly
the fs13 wall's composition. Narrow-universe exact planes (separate
dense id space for exact-minted rids) is the engineering lever; until
then a kernel-scale run extrapolates to ~30 h.

**Soundness.** t_container 2/2 under the gate (container_of exact — the
old flows-to shift blowup does not manifest at this marking density);
t_maskwalk all three routes; t_ops/t_pairs/t_allocinit exact; smoke 4/4
with the gate off (defaults untouched).

## Task #39 round 2: containment closure null + the fs13 decomposition (km, 2026-08-04)

The user pointed at the StructAnalyzer: `StructInfo::containers` already
records every embedding struct, so the nexus name set now closes
transitively over containment (bpf_link -> bpf_tracing_link; 20 listed
-> 174 types at km). **Verdict: NULL** — byte-identical to the
no-closure run (-1,875/+0). The embedded-type hypothesis for the fs13
gap is falsified as-tested.

Bound modes settle where fs13's discrimination actually lives:

| mode | exact roots | km removals | share of fs13 | time |
|---|---|---|---|---|
| default 6-type list | 212 | -1,846/+0 | 41% | 17.5 min |
| widened 20 (+closure) | 281 | -1,875/+0 | 42% | 18.4 min |
| `all` (every struct object origin) | 3,297 | -3,092/+0 | 69% | 22 min |
| `all+ids` (+ nexus-marked identity roots) | 8,227 | -4,443/+0 | **98.8%** | 31 min |
| full fs13 (everything exact incl. fn) | 46,869 | -4,499/+0 | 100% | 80 min |

Reading:
- **Identity-root residues carry ~30% of fs13's discrimination** (the
  bpf_link_release / tracing_stat_open block): the shared-helper
  formal (`bpf_link_init`-shaped) is the join witness, and its exact
  residues separate the ops-field cell from the rest — object origins
  alone cannot reproduce this because the helper pools every caller's
  objects through one formal.
- **Fn-exactness is worth 56 pairs for +49 min** — fn@X is essentially
  free precision-wise and over half of fs13's cost.
- **Cost model corrected**: RSS is constant (8.6 GB) from 212 to 8,227
  exact roots, and time fits ~15 min FLOOR + ~1.7 min per 1,000 exact
  roots (extrapolating to fs13's 80 min at 46,869). The floor is NB>0
  structural overhead (presolve under field labels, per-class plane
  sweeps), NOT plane width — so the earlier narrow-universe idea
  attacks the linear term, and the floor needs its own profile before
  a kernel-scale run is priced.

Every mode is removals-only vs FI and (except 56 pairs) a subset chain:
default ⊂ all ⊂ all+ids ⊂≈ fs13. The practical instrument today is
`all+ids`: 98.8% of full field sensitivity at 2.6× less cost.

## Task #40: origin-batched solving — prototype verdict (km, 2026-08-05)

`--cfl-batch-roots=K` (f2a9b16), built off the user's decomposition
question: if the kernel is modular, sub-problems should solve in
bounded memory. The right axis is ORIGINS, not subsystems: fact planes
are pure derived state, so per batch the solver releases every plane,
seeds K roots, drains, and harvests answer bits; only the union-find
quotient, join keys, and bridges persist (megabytes — no disk, unlike
Graspan-style offload: recomputation from the retained quotient is
cheaper than I/O). Rounds repeat until a pass adds no merges; monotone
merges terminate this at the same closure.

Verdict (km, K=4000):
- FI: BYTE-IDENTICAL to monolithic, 2x time. Rounds: 22,288 / 50 / 0
  merges — 99.8% of the quotient forms in the first pass. THE
  MODULARITY THESIS, OPERATIONALIZED AS ROUND COUNT.
- all+ids (full surgical fs): BYTE-IDENTICAL (50,199), 3h07 vs 31min
  (6x), peak 7.77 vs 8.57 GB. Rounds per CG iteration: ~43.7k / ~450 /
  0 — stable 3-round convergence.
- Memory win is modest at km because the km floor is graph+presolve;
  the plane share batching cuts is the ~200 GB term at kernel scale
  (the 700 GB-machine run observed 253 GB RSS).
- Time overhead = per-batch fixed sweeps of hot shared classes ×
  batches × rounds × CG iterations. Tuning levers: larger K, skip the
  redundant harvest work in non-final rounds, and parallel batches
  (the BSP pool already exists). Guards: incompatible with
  --cfl-lazy-mint / --cfl-verify-closure.

Also caught: kmdef.s was a STALE baseline (predates cone default-on);
fresh kmdef2.s differs by exactly the cone -1,184/+0. All relative
session conclusions stand; true fs-only shares: default -662, all
-1,908, all+ids -3,259 of fs13's -3,315 (98.3%).

## Task #41: process-parallel batches — fork/CoW workers (km, 2026-08-05)

Motivated by the big-machine kernel all+ids OOM (289 GB peak on the
700 GB box at 8h35m, near-allyes-class corpus) and the user's
directive: more cores than memory — parallelize what fits.

`--cfl-batch-workers=P` (00cf6b0): fork P workers after graph build.
The graph and quotient arrive COPY-ON-WRITE — no reload, no
duplication; memory = graph(shared) + P live batch plane-sets, sized
directly by P and K. Workers drain single-threaded (fork does not
carry the wave pool's threads; all parallelism is processes), record
their EFFECTUAL events — first-time cluster-key inserts + every merge
— plus harvested fptr bits to /tmp scratch files, and _exit. The
parent replays streams in worker order: replayed inserts recreate
keys/VX bridges, cross-worker key collisions become the cross-batch
merges. This is the Jacobi form of the sequential rounds (one extra
round: km all+ids converges 43k/…/86/0 in 4 rounds vs 3 sequential),
terminating at the same closure by merge monotonicity.

km validation (all byte-identical to monolithic):
- FI K=4000 P=4: 2:21 wall (sequential batches 3:30, monolithic
  1:44), RSS flat 3.13 GB, 82,998 events replayed (≈3 MB streams).
- all+ids K=4000 P=6: 49:47 wall — 3.8× over sequential batching,
  1.6× over monolithic — peak 7.84 GB.

Big-machine recipe: --cfl-nexus-fields=all+ids --cfl-batch-roots=K
--cfl-batch-workers=P with #batches ≈ 4P for balance; peak ≈
graph+presolve + P×(plane total/#batches); start P=8 and raise while
RSS fits. RLIMIT_AS (--mem-limit) is per process and each child's AS
includes the shared mappings — set it generously. Workers dirty the
union-find via path compression (CoW duplicates those pages) — small
(8B/class).

## Bridge note (2026-08-10)

Tasks #42–#48 were logged in commit messages and session records
rather than here: #42 batch spill (zstd ~600×), #43 incremental
exactness fix (stale bidi cone, b82985d), #44 body-skip recall fix
(+1,038 km), #45 AddressTakenFuncs canonicalization + boundary
census, #46 COW plane sharing (a997bc1), #47 bundling probe NO-GO
(falsification #8), #48 cluster-mark join fast path (32d8793,
lookups 39.94M→96k). See docs/design-section.md notes and the
kernel-idchan / kmdef2 pins. This log resumes with the
field-sensitivity worthiness arc.

## Task #49: fs worthiness at kernel scale — the same-IR A/B (2026-08-09/10)

The 70h20m/365 GB big-machine run (kernel-nexus-allids, old binary)
was the FIRST kernel-scale field-sensitive completion — feasibility
proven, no caps, exit 0, 5 wiring iterations × 3 batch rounds with
round 3 = 0 merges every time (the batched_exact closedness
hypothesis discharged in the log). But worthiness needed a
same-binary A/B, and pins do not travel across IR builds
(SSA/metadata renumbering: zero common lines — eval/50-compare.sh
now aborts on that).

HEAD FI on the same 6.18 bclist: 4,866,847 pairs / 16,512 sites /
2:07:18 / 22.6 GB (kernel-fi-618, new FI baseline). Same-IR compare
vs the fs run, vintage-decomposed:
- net −2.25%; of which 32,696 "removals" at 86 fs-absent sites are
  binary vintage (#44 recall in FI only) — partly ALSO real
  site-emptying (same-binary km shows fs legitimately empties
  slice-truncated sites: bpf_link_release 532→0);
- genuine selective-fs tightening ≈ 80,868 pairs (−1.66%) at 7,694
  sites — mostly shallow, PLUS 73 deep-collapse sites (≥90%
  reduction, 18,376 pairs): acpi_ev_fixed_event_detect 1800→3,
  __netlink_dump_start 1800→4 — removed populations are ONE shared
  hub cone (netlink∩acpi removed overlap 1,793/1,796), survivors
  are the true registrants.
- CORRECTION: fs "sound recall" (+895 in the old km compare) was
  kmdef2 vintage — same-binary km all+ids adds ZERO pairs over FI.
  container_of recall claims stay micro-scoped until a kernel-fs
  HEAD run.

Mechanism verdict: the giant's dominant conflation is SAME-OFFSET
registration mixing (fanout max 4,424→4,367 under fs — hubs
intact); fs only cracks the cross-field artifact mode (~2%).
Targeted fs (detector-suggested nexus lists, km): capture 27%→60%
of the all+ids ceiling with outer-struct closure (bpf_link for
bpf_link_ops), but cost is NSHIFT-STRUCTURAL — 1,104 exact roots
already cost 24 min vs FI 1:49 vs ceiling 34:24 (plane scans
~4.7×/solve + no incremental under fs). Root-population is not the
dial; plane-occupancy skip is the (unbuilt) engineering lever.
Verdict: fs = instrument and reference, NOT an operating point;
the deep collapses belong to channels.

## Task #50: auto-certified identity channels (regfield) — detector, apply, audit (2026-08-10)

The deep-collapse signature is detectable from ONE FI run: a
(struct+offset) registration field whose WITNESSED store population
is narrow while resolved reader fanout is wide. --cfl-regfield-report
(196e293, 5d11e22): population from constant stores + install-API
argument hop + global-initializer slots + copy-edge closure
(control-struct relays); two-level dispatch must suggest the
ops-POINTER holder too (without bpf_link, bpf capture was 11/532).

--cfl-regfield-apply (8ea40b1): keys whose population is
machine-certified CLOSED (every mutation path classified; hazards at
zero: unwitnessed stores, atomics, non-const bulk copies, escaping
slot addresses, var keys) become channels in the SAME run —
resolution at reader sites intersects the table; open keys are
untouched (same-slot instance pools look exactly like unwitnessable
populations, correctly refused). Two certifier bug classes caught
during km bring-up: any-caller witnessing (partial tables could
close) and indirect-caller arg-hop (smear-resolved callers pollute
tables — clear_page_erms entering irqaction+0).

Audit (16cfdb4): (1) AT-unused delta = 0/3,715 at kernel — −1.49M
pairs de-dispatched no function entirely; (2) provenance
certificates per key: GREEN const-init-only (rodata-structural) /
YELLOW hazard-dependent / ORANGE copy-closure-dependent; (3)
semantic sampling vs source found a REAL hole — whole-struct stores
through bare pointers (*work_buf = {.fn = fn} in
stop_one_cpu_nowait) were invisible AND unhazarded; fix opens the
value's struct type (ditto bare-ptr memcpy via alloca type); the
remaining blind spot (scalar fn stores through bare pointers) is a
COUNTED residual, not prose.

AUDITED KERNEL PIN (kernel-fi-autochan2, binary 16cfdb4): 1:46:37 /
22.4 GB (vs FI 2:07), 1,997 closed keys / 8,087 sites /
−1,487,417/+0 = −30.6% ON TOP of the hand-built channels; answers
3,379,430 pairs, STRICT SUBSET of FI verified; fanout p50 43→6,
p90 540→444, max unchanged (hubs = open keys, correct). Hole fix at
kernel scale = 1 key de-closed (keyring_search_context+88),
restoring 572 true-risk pairs at search_nested_keyrings — the
predicted FN class, caught by the audit. Certificates: 1,105 GREEN /
869 YELLOW / 23 ORANGE (the ORANGE list is the designed relay set:
netlink_callback+24, netlink_sock, efivar_operations, Qdisc+8,
hc_driver). Residual: 273 bare-pointer fn stores kernel-wide.

Contrast that closes the precision ladder: selective fs −1.7% at
20–30× cost; auto-channels −30.6% at NEGATIVE cost, one run, a
certificate per key. Three-tier channel arc: hand-derived (−32%) →
census-confirmed (INVOKE) → auto-certified (−30.6% more).
Eval: ftc mode in eval/30-run.sh runs ft+apply+audit with a built-in
strict-subset gate (8f2db62). Open tail: eyeball the 23 ORANGE keys
vs source; kernel-fs HEAD run for the recall question; ORANGE→GREEN
upgrades via rodata-source tracing if wanted.

## Task #51: fs-cost probe day — two falsifications and the real profile (km, 2026-08-14)

Question: why is fs 56× FI (km fs41 4h13m vs 273s)? Two candidate
levers died honestly. (1) Plane-occupancy skip masks: implemented,
A/B byte-identical AND wall-flat (15,074s vs 15,204s) — occupancy
probe showed 93% of planes LIVE at pop and empty-plane scan at
0.005% of cycles; reverted with tombstone (8b91235). (2)
FI-prunes-fs (the PLDI'20-inspired simplification): the sound
all-derivations keep-set (CONE-ACTIVE origins on fptr-ancestor
classes) covers 52.5% of roots but 99.98% of fact mass — the hub is
an fptr-ancestor, so sound pruning removes nothing; only the
retired filter's unsound mode ever had anything to delete. What the
day actually bought: SolverProf attribution (join 69.5% of pop
cycles POST-#48 — 9.0B cluster-mark skips at ~350 cycles each vs
1.8M real lookups), --log-timestamps, and origin co-travel sizing
(53,794 roots → 33,358 distinct columns, fact compression 3.21× at
FI). Levers ranked: join-work engineering, bundles, channels.

## Task #52: cell-major join sweep + batch-mode grid marks (km, 2026-08-15)

The join filter was fact-major: ~350 cycles (find() chase + random
bit probe) per (fact,cell) visit, 99.98% proven no-ops — merge
re-offers re-confirming absorbed planes. Inverted to cell-major
(f13f8d6): per cell, one read-only subsetOf word scan (with the
interned pointer fast path) certifies "cluster already absorbed the
whole backlog"; word-ANDN residual; per-fact work only for first
joins; per-fact joined marks became one end-of-sweep word-OR (sound
because the outer bound re-reads cellsOf, so merge-appended cells
see the same backlog). km fs41 byte-identical, 15,201s → 9,321s
(1.63×), join 69.5% → 33.1%. Then batch mode (d105585): workers had
NO fast path at all (the #48-era batch OOB = dense promotion sized
to the batch-local universe — fixed by sizing promote() to content);
marks moved to GLOBAL grid space (valid across batches/rounds —
registry global, clusters only grow), backlog imaged per sweep by a
word-shifted copy valid for any rid base. km fs13 batched 69m29s →
25m18s (2.75×), event-replay structure identical, byte-identical;
mono == batched re-pinned at HEAD.

## Task #53: origin-equivalence bundles — proven exact, parked on economics (km, 2026-08-15)

Design + Lean core first (781d506): bundle_exact (a quotient of
closure-row-equal origins preserves the closure member-by-member —
mixed-member join witnesses collapse via row equality) and
row_determined (equal carried-base rows ⇒ equal closure rows = the
drain-checkpoint full-state-hash test); L1 coupling lemma
(joinCluster merges clusters through shared cells, so co-traveling
origins' memory nodes are already one class — bundling shares
nothing new); addFact audit → no split protocol needed (facts only
enter at rid birth). Gate 0 passed with margin (fs13 root ratio
1.95×, fact compression 4.84×, max bundle 31,771 = 43% of active
roots). Epoch coarsener shipped default-off (adc1d31); the L1
assertion earned its keep TWICE: a partition-refinement pre-split-
size bug, then a genuine theory gap — row equality does NOT imply
cluster equality at a checkpoint (the registry is MEMOIZED join
history; merge's joined-intersection erases the row evidence) → the
epoch test refines on (presence, cluster class) per shift. Gate 2:
km fs13 BYTE-IDENTICAL through 2 epochs (74,891 → 48,910 ids) +
expansion, every assertion silent — exactness validated at scale —
but 157m54s vs 32m27s: epochs stream O(live mass) against 230s
drains, co-travel forms late, and the compression dies at expansion
and from-scratch rebuilds. PARKED (falsification #10-ish, of the
economics not the theory). Decider: fs41 batched 108m vs mono 155m
byte-identical — batching subsumes the width lever (K-wide batch
planes), bundles CLOSED (5bac7ad).

## Task #54: fused delta-OR kernels + BitPlane; two layout falsifications (km, 2026-08-15/16)

addBits/addBitsBridged paid ~16 plane streams per effective OR;
fused dense tails do it in two loops (delta with inline any +
popcount; one OR loop into all targets), with the #46 adopt/interned
fast paths preserved in front (c61ae11). Dense storage moved off
llvm::BitVector (private word storage — user directive: no
LLVM-internal APIs, self-contained) onto src/lib/BitPlane.h, ~150
lines mirroring the consumed API with honest mutable words. km fs13
mono 32m27s → 23m21s, fs41 mono → 1h49m, fs41 batched → 1h32m, FI →
3m55s; a-prop and f-prop each ~3×; ALL byte-identical. Then two
falsifications: merge-block fusion (c1122a8) — byte-identical but
wall-flat with merge cycles +14%; the merge bucket's mass is the
jdirty-re-offer/joined-intersect unionWith traffic whose COW adopt
paths a word loop destroys, reverted with tombstone. Slab/chunked
layouts (d51133e) — falsified PRE-BUILD by measurement: perf stat
showed IPC 2.76 with LLC misses ~1.4% of cycles (compute-bound, no
locality debt) and the occupancy probe showed streamed deltas
already 92.7% zero-word-skipped. The earlier "2.4 GB/s vs 15 GB/s
headroom" arithmetic was the multi-pass overhead the fusion
harvested, not latent bandwidth.

## Task #55: presolve-once — the hidden 56% and the #43 attribution (km, 2026-08-16/17)

With the solver at its compute floor, wall decomposition (timestamps
+ the 4.5-CPU utilization anomaly) exposed a single hidden phase:
the pre-solve sublanguage saturation RE-RUN on the post-wiring graph
— a one-time giant-SCC discovery costing 56% of fs41 wall (~3,700s)
and ~600s at fs13, invisible for months inside bigger numbers.
--cfl-presolve-once (cd67728 — note: the core guard nearly shipped
inert; the flag definition and the CallGraph.cc guard were split
across commits) skips iterations ≥ 1 and pulls the first in-drain
a-SCC sweep early. Verdicts: fs41 BYTE-IDENTICAL to the eager pin
(the smear family is a P=13 residue-collision artifact absent at
P=41) at 1.55× (mono 1h49m → 1h11m); fs13 strictly tighter — the
−504 pairs are ALL at opt_pre_handler, i.e. EXACTLY the task-#43
"incremental divergence": ATTRIBUTED to pool-smear manufactured by
the pre-solve re-run's coarsening, not to incremental solving. fs
INCREMENTAL thereby unblocked: fs13 incremental+presolve-once
byte-identical to the presolve-once scratch pin (150,238) at
13m52s. Combo gate with the canonical kernel config: bidi ==
bidi+presolve-once byte-identical (148,703 = no-bidi − 1,088 strict
subset; bidi is tighter under fs, not answer-invariant — flag-match
pins), fs41 batched+bidi+presolve-once = 27m22s. SESSION ARC: km
fs41 4h13m → 27m22s (9.2× on the canonical lineage), fs13 → 13m52s,
FI → 3m55s, every step byte-identical or attributed. Falsified en
route: --cfl-presolve-exact as kernel insurance — OOM-killed the
62GB box in ~3 min at fs41 batched; the GraCFL pre-solve quotient
is load-bearing for MEMORY (uncollapsed born-giant = the ~1000×
plane replication, unfused). Kernel HEAD re-run restarted at
cd67728 with the validated command (initial sublanguage graph
36.4M edges = 15× the old vintage's 2.4M — the recall work's
legitimate edges; ~68 saturation iterations expected for the
all+ids family). Organized version of #51–#55:
docs/implementation.md.
