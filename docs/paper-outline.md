# Paper outline — Why CFL-Reachability Doesn't Scale, and What Does

Status: draft outline (2026-08-06, rev 2: the scaling diagnosis is the
opening act — the project BEGAN as "why can't the CFL solver scale?", and
the paper's spine is that question answered, then each successor wall
diagnosed and removed the same way). Numbers cite the canonical pins and
the task log; items marked [PENDING] depend on runs still in flight.

## Title candidates

1. *Why CFL-Reachability Doesn't Scale — and How to Make It: Sound
   Flows-To Call Graphs for the Linux Kernel on a Desktop*
2. *The Quadratic Ghost: Diagnosing and Dismantling the Scaling Walls of
   CFL-Reachability Pointer Analysis*
3. *ORCFL: Answer-Anchored, Resource-Bounded Pointer Analysis for
   Multi-Million-Line Monolithic Systems*

## The origin story = the framing device (added 2026-08-07)

The project began as an adjudication between two expert claims that
cannot both be true as stated:

- The SECURITY practitioner's claim (Zhiyun, KallGraph): pointer-
  analysis scalability for kernel call graphs is UNSOLVED — that is
  why KallGraph needs resource heuristics (verified in their released
  code: 35-edge path cap, dynamic top-50 hub blacklisting, blocking
  formals of >250-caller utilities; see
  docs/novelty-and-related-work.md KallGraph dossier).
- The GRAPH-ENGINE researcher's claim (Zhijia, GraCFL): CFL-
  reachability scalability is SOLVED — best-in-class engines chew
  through billions of edges with minimal redundancy.

RESOLUTION (the paper's thesis, provable with our measurements): both
are right at their own layer and the wall lives BETWEEN them.
- The engine layer is solved (Zhijia right): GraCFL outperforms POCR
  on our graphs; no engine defect is in play. But an engine's work is
  lower-bounded by its OUTPUT, and over LLVM-IR graphs the closure
  itself is Θ(Σ|a-component|²) — the best engine hits the
  formulation's floor faster (OOMs on harfbuzz, a library).
- The practitioner's pain is real (Zhiyun right): whole-kernel icall
  analysis does not fit — but the caps are the demand-side SYMPTOM of
  the same wall, not a solution: every deep query re-explores the
  giant may-alias component, so the DFS must either drown there or
  silently truncate it. The caps fire exactly where the answers are
  hardest (and truncation masquerades as precision).
- What the reconciliation forces: neither more engine nor capped DFS,
  but a REFORMULATION whose output is small enough to solve —
  answer-anchored flows-to (Σ|C|·answer-relevant origins) — then
  real graph-processing discipline applied to THAT problem
  (delta/wave propagation, union-find joins, origin batching):
  whole-program solving amortizes exactly the cross-query redundancy
  that per-query DFS re-pays 159k times per fixpoint round.

Intro hook sentence candidates: "Depending on whom you ask,
CFL-reachability pointer analysis either scales, or it does not —
and both answers come from experts holding state-of-the-art
results." Then: both are right; the wall is the formulation's output
size, invisible from either side because each side's own layer is
healthy. (In the paper, cite the two lines' results rather than the
personal communications; the code-verified caps make the security
side's position citable.)

## Positioning (the spectrum, and who we must convince)

- ONE END: type-based resolution. Scales trivially; the community knows
  its limits and has spent a decade compensating ad hoc (MLTA-style
  multi-layer refinements, per-pattern filters). Under opaque pointers
  the type signal itself is eroding. We are NOT another patch on this
  end.
- OTHER END: CFL-reachability. Sound by formulation, with a rich engine-
  scalability literature (Graspan, POCR, Pearl, GraCFL) whose authors —
  including our colleague, GraCFL's author — reasonably believe the
  scalability problem is SOLVED. Our claim, stated precisely: it is
  solved at the ENGINE level and open at the FORMULATION level. An
  engine's work is lower-bounded by the closure it must materialize;
  over LLVM IR (assistant cells per load/store, copy chains, whole-
  program linkage) the closure itself is Θ(Σ|a-component|²). We ran the
  best engine (GraCFL, which outperforms POCR on our graphs) on the
  standard encoding: it OOMs on harfbuzz — a LIBRARY. Optimal engines
  hit the formulation's floor faster; that is demystification, not
  contradiction — the engine line's success is what ISOLATES the
  residual wall.
- THE ESCAPE HATCH THAT ISN'T: demand-driven CFL (Heintze-Tardieu,
  Sridharan-Bodik, Boomerang-style) answers single queries. A call
  graph is uniquely WHOLE-PROGRAM: every icall site is a query (18,189
  of them), the queries share nearly all their work through the giant
  component, and resolution FEEDS BACK (resolved targets wire new
  callee edges that change every other query) — so on-demand
  degenerates to all-demands iterated to a fixpoint, re-paying the
  closure per round. What a call graph needs is a formulation that is
  whole-program in COVERAGE but demand-shaped in FACT MASS.
- OUR POINT ON THE SPECTRUM: answer-anchored flows-to = all demands at
  once. Anchor the fact space at origins (the alphabet answers are made
  of), prune to the answer cone (bidi oracle: ~14% of roots are answer-
  relevant), integrate the wiring fixpoint into one monotone solve.
  Sound like the CFL end, scalable like neither end could deliver:
  better than iterative on-demand by construction, not by tuning.

## The narrative spine (the staircase of walls)

W0. SATURATION WALL: pairwise V saturation is quadratic — V fact mass ≈
    Σ|a-connected component|² — so the closure, not the graph, is what
    explodes (harfbuzz OOM at library scale; graph dedup and RSM folding
    tried and abandoned because they shrink the graph, not the closure).
    DIAGNOSIS FORCES: stop materializing pairwise V; anchor facts at
    origins → answer-anchored flows-to ((origin, shift) planes, witness
    joins). Mass drops from Σ|C|² to Σ|C|·(live origins), and the kernel
    becomes solvable (20 min, first sound whole-kernel run).
1.  PRECISION WALL: the may-alias quotient concentrates 93% of answers in
    one class → anatomy (§4), identity channels (§5), surgical fs (§6).
2.  FS FACT-MASS WALL: field residues re-fragment the quotient and the
    QUADRATIC GHOST RETURNS as replication — fragments each carry their
    flow-through sets (124B facts, 70x). Same diagnosis shape as W0:
    the mass is redundant copies. → origin batching + spill; the 600x
    spill compressibility is the replication made visible (the RAM cost
    and the disk discount are the same phenomenon).
3.  RESOURCE WALL: address-space vs resident memory, dense-plane width,
    allocator reservations → batch-local universes, CoW workers, RSS
    watchdog; memory becomes a dial, byte-identical throughout.

## One-paragraph abstract (draft, rev 2)

Indirect-call resolution spans a spectrum: type-based matching scales but
over-approximates by an order of magnitude despite a decade of ad-hoc
refinement, while CFL-reachability is sound and — after a rich line of
engine research — widely believed to scale. We demystify the latter
belief for the setting that matters: over LLVM-IR graphs, the
best-in-class engine exhausts memory on a single LIBRARY, because the
wall is not engine throughput but closure size — pairwise alias
saturation materializes a fact set quadratic in the a-connected component
mass (V ≈ Σ|C|²), a floor no engine can beat and graph compaction cannot
touch. Nor can demand-driven analysis rescue call graphs specifically:
every call site is a query, queries share their work through one giant
alias class, and resolution feeds back into every other query — a call
graph is irreducibly whole-program. This diagnosis forces a formulation
that is whole-program in coverage but demand-shaped in fact mass: ORCFL
anchors facts at origins — (origin, field-shift) pairs joined through
witness-exact cluster unification — making fact mass linear in component
size times answer-relevant origins, and yielding the first sound
whole-kernel flows-to call graph, 10.8x tighter than type-based
resolution. Scaling then fails three more
times, and each failure is the same phenomenon in a new costume. The
precision wall: 93% of resolved pairs ride a single may-alias quotient
class, which we show is born from connected-component over-unification
and sustained by fact accumulation through a small set of semantically
real rendezvous channels (task_struct, tracepoint argument pools); the
kernel's object plane is otherwise bimodally modular (cross-subsystem
welds are 0.98% of merges). Dispatch families whose function identity the
quotient destroys (tracepoints, static_call) are recovered exactly at
answer level from census-complete binding tables — removing 32% of
resolved pairs while making the analysis faster. The field-sensitivity
wall: exact residues re-fragment the quotient and the quadratic mass
returns as replication (124 billion facts, 70x the kernel/ subset);
gating residues to nexus-typed origins recovers 98% of full field
sensitivity at a third of its cost. The resource wall: origin-batched
solving — facts are per-origin, so only the join topology is shared —
with copy-on-write process parallelism and compressed plane spilling
(600x, because replication IS compressibility) bounds memory to one
batch's working set, enabling the first kernel-scale field-sensitive run
on a 62 GB desktop. Batched, parallel, and spilled modes are
byte-identical to the monolithic solve; the staged-exactness arguments
are machine-checked in Lean. On the 6.8 kernel, ORCFL resolves 18,189
indirect call sites to 5.69M pairs — 10.8x tighter than type-based — in
under 3 hours.

## Contributions (the reviewer-facing list)

C0. **The scaling diagnosis.** Why CFL-reachability solvers hit a wall:
    the closure, not the graph — pairwise V saturation materializes
    Θ(Σ|a-component|²) facts, so graph dedup/folding cannot help (both
    tried, both null at library scale: the honest negative results).
    The diagnosis predicts and explains the later walls too: field
    sensitivity re-fragments components and the quadratic mass returns
    as per-fragment replication — measurable directly (124B facts) and
    visible as the 600x spill compressibility (redundant copies
    compress). One phenomenon, three costumes.

C1. **Answer-anchored flows-to formulation** (the reformulation C0
    forces). Facts are (origin root, net field shift) pairs; memory
    aliasing is a join keyed by shared-origin witnesses; union-find
    clusters replace pairwise V saturation. Fact mass drops from Σ|C|²
    to Σ|C|·(live origins). Sound-by-construction; first sound
    whole-kernel flows-to call graph; 10.8x tighter than type-based.
    (Position against BidirectedReach/POPL'18: the join layer is a
    rediscovery, witness-exact unification + Z_P shift residues +
    certificates are new — see docs/novelty-and-related-work.md.)

C2. **The identity-channel principle.** When the may-alias quotient
    absorbs either endpoint of a dispatch registration, no graph-level
    refinement can recover it; resolution must consume census-complete
    binding tables at ANSWER level, with loud completeness counters that
    must read zero. Instantiated for tracepoints (-1.50M pairs, 17.9%)
    and static_call ops tables (-1.20M, 14.3%): combined -2.70M pairs
    (32% of the pin) with every removal certified -N/+0, and the solve
    got FASTER (2.98 h, -28%).

C3. **Anatomy of the quotient.** A falsification-driven measurement
    campaign showing: (a) the giant is BORN from Steensgaard-style
    connected-component merging (true mutual-flow core: 41 of 41,350
    nodes); (b) it persists by fact accumulation, not class merging
    (0/4,733 fn classes merged; 1,389 diffuse entry cells); (c) the
    object plane is bimodally modular — cross-subsystem welds are 0.98%
    of merges, and the surviving couplers under field sensitivity are
    semantically true task-rendezvous channels (current, tracepoint
    argument pools), not analysis artifacts; (d) nexus discovery ranks
    the coupling carriers (list_head #1, task_struct #2) and splits them
    into intrusive links vs fat objects, each wanting a different remedy.

C4. **Surgical field sensitivity.** Exact field residues gated to
    nexus-typed origins: wildcard-minted origins are provably
    field-insensitive-identical, so cost scales with the gated
    population. Decomposition result: object origins alone = 69% of full
    fs; + identity roots (shared-helper formals) = 98.3%; function roots
    never need residues. The dial: 20% of fs at 9x cost ... 98% at ~16x,
    vs 43-48x for full fs.

C5. **Resource-bounded solving, exactly.** Origin batching (facts are
    per-origin; the only shared state is the join topology), fork/CoW
    process parallelism with effectual-event replay, batch-local fact
    universes, and zstd-streamed plane spilling. All modes byte-identical
    to monolithic at every gate; staged/batched/spilled exactness
    machine-checked in Lean (SDeriv/WDeriv theorems: catch-up confluence,
    batched_exact, spill confluence). Memory becomes a dial: kernel
    field-sensitive solving runs on a 62 GB desktop [PENDING: completion
    of kernel-nexus-spill2 run] and the modularity thesis is
    operationalized as round count (99.8% of merges land in round 1).

C6 (maybe folded into C3). **Methodology: falsifications as results.**
    Three "emergent-scope" falsifications (seal, tracepoint cells, rodata
    copy-not-unify) establish a reusable pattern: probe removals are not
    a semantic prize until an honest model reproduces them. Plus the
    stale-baseline and byte-identity disciplines.

## Section-by-section

### 1. Introduction (1.5 pp)
- Open with the two-claims hook (see "The origin story" above): the
  security line says scalability is unsolved and caps its traversals;
  the engine line says it is solved and has the benchmarks to prove
  it. Both are state of the art. Who is right? (Answer: both, and the
  wall is between their layers — the formulation's output size.)
- Why the answer matters downstream: sound indirect-call resolution for
  CFI policy size, fuzzing reachability, patch impact; type-based is
  both too loose (10.8x) and structurally untrustworthy under opaque
  pointers.
- The staircase: W0 saturation (quadratic closure) -> precision (the
  quotient) -> fs fact mass (the quadratic ghost returns) -> resources.
  Each wall diagnosed by measurement, then removed by a design the
  diagnosis forces.
- Contributions bullet list (C0-C5/6).

### 2. Measurement study: what a kernel call graph actually requires (2–2.5 pp) — C0, W0
DEDICATED PRE-DESIGN MEASUREMENT SECTION (decided 2026-08-08; draft in
docs/measurement-section.md). Carries ONLY tool-independent
measurements; adjudicates the two-colleague dispute with data; ends
with requirements R1–R4 that §3 (design, docs/design-section.md rev 2)
opens from. Two subsections: 2.1 the closure wall (below), 2.2 the
dispatch-fabric census (asm 129,812/13.7%, int-provenance 47,676,
PREL32 section arrays, patching families, extern boundary closed) —
moved here from the old design §3.2; §4 anatomy stays mid-paper
(tool-produced measurements); §8 eval keeps outcomes only.
- The setting that makes the claim precise: LLVM-IR-level graphs
  (assistant cell nodes per load/store, copy chains from SSA, whole-
  program linkage — millions of nodes BEFORE closure), not the smaller
  pre-abstracted graphs much of the engine literature evaluates on.
- The saturation baseline (per-TU compositional CFL over the P2 grammar,
  GraCFL engine — best-in-class, outperforms POCR on these graphs):
  correct at libpng scale, OOM at harfbuzz — a LIBRARY, two orders
  below the kernel. The engine is at its floor; the floor is the
  problem.
- The autopsy: closure size, not graph size. V is an equivalence-like
  pairwise relation materialized fact-by-fact: |V| ≈ Σ over a-connected
  components |C|² (measured curve). The two remedies everyone reaches
  for — global dedup, RSM graph folding — implemented and NULL: they
  shrink the graph, the closure doesn't care. (Negative results stated
  as results.) Engine work is lower-bounded by output; no engine
  research can remove an output-size wall.
- Why on-demand is not the rescue for THIS problem: call graphs are
  whole-program (all sites are queries; queries share the giant's work;
  resolution feeds back into every query). Iterated on-demand = the
  closure re-paid per fixpoint round.
- What the diagnosis forces: never materialize pairwise V; index facts
  by origin — whole-program coverage, demand-shaped mass. Preview:
  Σ|C|² -> Σ|C|·(live origins), origins prunable to the answer cone
  (bidi oracle, ~14% answer-relevant), wiring fixpoint integrated.

### 3. Answer-anchored flows-to (1.5 pp) — C1
- The reformulation: mint origins, propagate (origin, shift) planes,
  join cells via shared-origin witness clusters (union-find); a/d/f
  edges, shift monoid + wildcard ⊤, Z_P residues as a monoid quotient.
- First sound whole-kernel run (14,799 icalls / 5.1M pairs, ~20 min) —
  the wall W0 is gone; witness-exact joins keep it sound (no silent
  fallback anywhere: completeness counters, assertions).
- Soundness schema (Lean: FDeriv vs SolverClosure, origins_minted; the
  July minting bug as a violation caught by the model; the five-node
  necessity counterexample).

### 4. Anatomy: where imprecision lives (2 pp) — C3
- 4.1 The giant: 93% of pairs ride one class (fat-site census: 5.3M
  pairs, 6,138 sites); born vs sustained (presolve over-unification;
  fact accumulation forensics; diffuse entry).
- 4.2 Modularity thesis: coupler census, bimodal diversity histogram,
  welder taxonomy (couriers / honest neighbors / allocator); the
  presolve-cone lever (-201,724 free).
- 4.3 Nexus discovery: ptr-write subsystem diversity ranking; class A
  (intrusive links) vs class B (fat objects); what survives under fs
  (task rendezvous — semantically true flows).
- 4.4 Falsifications (table): fragmentation hypothesis, int-provenance
  residues, embedded-type hypothesis, emergent-scope pattern x3, born=
  exact. Each: claim, probe, honest-model verdict.

### 5. Identity channels (1.5 pp) — C2
- The principle + why graph-level attempts fail (tracepoint cells v1/v2
  autopsy: fn identity is a casualty of V-merge).
- Tracepoint keys: census-complete walker (trace_event_call /
  __bpf_raw_tp_map), completeness counters, kernel -1.50M/+0.
- Static_call ops tables: initializer inventory, table-authoritative vs
  type filter (return0), kernel -1.20M/+29-real.
- The INVOKE family (pair-correlated dispatch) as the earlier instance;
  design rule: identity lives at answer level until provenance cells
  exempt fn identity from the quotient.
- AUTO-CERTIFIED TIER (added 2026-08-10): the channel signature is
  detectable from one FI run (narrow witnessed store population vs
  wide reader fanout); closedness certifier (4 population sources, 5
  hazard counters) auto-closes 1,997 kernel keys -> -1,487,417/+0
  (-30.6% ON TOP of hand channels), fanout p50 43->6, negative solve
  cost, single run. Audit trail as artifact: GREEN/YELLOW/ORANGE
  provenance certificates (1,105 rodata-structural), counted 273-store
  residual, AT-unused delta 0, and the caught certifier hole
  (whole-struct bare-pointer stores; 1 key, 572 restored pairs).
  Three-tier arc: hand-derived -> census-confirmed -> auto-certified.

### 6. Surgical field sensitivity (2 pp) — C4, W2
- Open by naming the ghost: residues re-fragment a-components, and
  per-fragment fact replication IS the W0 quadratic reappearing (48x
  facts at km, 70x at kernel — measured, and the cost model: floor +
  linear in exact roots).
- The gate: wildcard-minting = provable FI-equivalence per origin; fn@X
  free; containment closure via struct layout (and its null result).
- The decomposition table: default list / all / all+ids / fs13 with
  removals, share, time. Identity residues = 30% (the bpf_link_init
  shared-formal mechanism — ties back to the store-hub finding).
- Recall, not just precision: fs adds sound pairs (member->container
  composition), i.e., FI is not an over-approximation of fs answers.

### 7. Resource-bounded solving (2 pp) — C5, W3
- Origin batching: planes are derived state; retained state = quotient +
  cluster keys + bridges (megabytes). Rounds to stability; modularity as
  round count (22,288/50/0).
- Fork/CoW workers: effectual-event replay; Jacobi vs Gauss-Seidel (one
  extra round); byte-identical matrix (table: mono/seq/P=4/P=6 x FI/fs).
- Batch-local universes: the dense-plane width cliff (42.5KB -> 2.5KB)
  — faster than monolithic at half the memory (29:30 vs 31:00, 4.5 vs
  8.6 GB at km).
- Spill: fold-through-find restore, touch-window re-offers, per-batch
  cursors; zstd 600x (replication IS compressibility — the RAM cost and
  the disk discount are the same phenomenon); RSS watchdog vs RLIMIT_AS
  (the 289-of-700 GB autopsy).
- Lean: WDeriv witness tables; batched_exact; wderiv_restore; what
  remains unverified (GAPS.md) — honest scoping.

### 8. Evaluation (2.5 pp)
- E0 Generality corpora (added 2026-08-08; first sound runs DONE,
  pins in ~/fast/ka-bench/): httpd 2.4.68+apr (339 TUs LTO bitcode:
  42s/0.75GB, 175M facts; type 400,968 -> CFL 108,282 = 3.7x; 1,191
  sites avg 91 max 344 = ap_hook pools) and postgres 18.4 backend
  (860 TUs: 5:16/5.9GB, 1.26B facts; type 2,382,359 -> CFL 398,698 =
  6.0x; 2,452 sites avg 163 max 3,271 = fmgr-shaped pool). Both give
  F0 curve points; both boundary ledgers populated (the census
  discipline transfers to userspace). Known channel candidates:
  ap_hook = CHAINREG-keyed (hook name = key); pg fmgr = static ops
  table analog. NOTE: fresh-IR corpora, NOT the Graspan-suite fixed
  graphs — never imply comparability with engine-paper tables; the
  suite-graph Σ|C|² experiment (§2.1 external validation) is separate
  and still TODO. SATURATION BARS DONE (2026-08-08, same IR graphs,
  GraCFL engine, 49GB cap): httpd OOM at 11:41, postgres OOM at 2:59
  — vs flows-to 42s/0.75GB and 5:16/5.9GB complete on the identical
  graphs. ≥65x memory (cap-censored) at httpd; the F0 exhibit no
  longer depends on harfbuzz alone. Logs: ka-bench/{httpd,pg}-sat.log.gz.
- E1 End-to-end: kernel 6.8 (2,618 objects), pin trajectory table:
  type-based -> flows-to v0 (14,799/5.1M) -> +summaries/invoke ->
  kernel-idchan (18,189/5.69M, 2.98 h, <45 GB). Sound micro suite +
  smoke gates.
- E2b FS-worthiness A/B (DONE 2026-08-10, same-IR 6.18): selective fs
  = -2.25% total (-1.66% genuine after vintage decomposition) at 33x
  wall vs auto-channels -30.6% at negative cost; km targeted-fs probe
  (detector-suggested nexus lists): 60% ceiling capture but cost is
  NSHIFT-structural, not root-population -> channels win the deep
  collapses; fs recall = 0 fs-only pairs at km HEAD (micro-scale
  container_of recall claims stay micro-scoped until kernel-fs HEAD).
- E2 Identity channels ablation (solo/union/synergy: removals =
  solo-union + 45,453 synergy exactly).
- E3 fs dial: cost/precision curve at km; weld census FI vs fs;
  [PENDING] first kernel-scale fs answer set + weld census (local run
  in flight; big-machine near-allyes run).
- E4 Batching matrix: byte-identity everywhere; memory/time envelopes;
  62 GB desktop kernel-fs run [PENDING]; big-machine recipe.
- E5 Comparisons: type-based; MLTA-class systems if feasible; discussion
  of unsound competitors (we refuse silent fallback).
- Threats: single kernel version/config; 63-bit subsystem mask (lower
  bounds); icall ground truth is approximate (removals certified -N/+0
  against our own sound baseline, not runtime traces).

### 9. Related work (1 p)
Organize as the three lines of the spectrum:
- Type-based + compensations: MLTA/TypeDive-class multi-layer matching,
  per-pattern kernel filters — the community's decade of patching the
  imprecise end; opaque pointers eroding the signal.
- CFL engine scalability: Graspan, POCR, Pearl, GraCFL — genuine
  successes AT THE ENGINE LEVEL; our measurements show the residual
  wall is the formulation's output size on LLVM-IR graphs (respectful
  framing: their success is what isolates it; we build ON GraCFL).
- Demand-driven CFL: Heintze-Tardieu, Sridharan-Bodik, Boomerang —
  single-query framings that call graphs structurally defeat
  (whole-program, shared work, resolution feedback).
- From docs/novelty-and-related-work.md: BidirectedReach/POPL'18 (join
  layer rediscovered; witness-exact unification, shift residues,
  certificates new), Graspan (offload: their closure IS the output; our
  planes are derived — recompute vs spill trade), POCR/Pearl/GraCFL,
  MLTA/TypeDive, kernel CFI (KCFI, IFCC), unification vs inclusion
  hybrids (our presolve IS Steensgaard — and §3 quantifies exactly what
  that costs).

### 10. Conclusion (0.25 p)
- The quotient is not a bug to fix but a structure to understand: its
  irreducible core is the kernel's real rendezvous fabric; everything
  else yields to identity channels, surgical residues, and
  resource-bounded exact solving.

## Figures / tables shortlist

- F0: THE SCALING CURVES — saturation V mass ~ Sigma|C|^2 vs flows-to
  ~ Sigma|C|xorigins vs fs replication, one log-log plot from libpng ->
  harfbuzz -> km -> kernel; the paper in one figure.
- F1: system overview (graph build -> presolve quotient -> batched
  planes/rounds -> answer-level channels -> resolution).
- F2: diversity histogram FI vs fs (the bimodal plot + weld kill).
- F3: fs cost/precision dial (removals vs minutes, 4 points + fs13).
- F4: batching matrix (mode x metric heat table, all "=" byte-identical).
- F5: round-convergence bars (22,288/50/0; 43.7k/450/0; kernel
  297,920/...).
- T1: pin trajectory. T2: identity-channel ablations. T3: falsification
  ledger. T4: memory autopsies (289/700, 43 GB floor, arena gap).

## Venue fit + scope cuts

- PL/SE systems venue (full story, 12 pp): as outlined.
- Security venue variant: lead with CFI policy-size reduction + the
  separation theorem (#32) as an application section; compress §6.
- If 10 pp: fold C6 into §3.4; cut §6 recall discussion to a paragraph;
  E5 comparisons to a table.
- Workshop/short fallback: §4 anatomy + §5 identity channels alone
  ("Where kernel indirect calls actually go").

## Claim-safety ledger (what we can assert today)

SAFE now: everything in C1-C4; batching/spill byte-identity at km scale;
Lean theorems; kernel identity-channel pin; round-1 kernel fs statistics
(124B facts, 297,920 merges).
[PENDING] before submission: kernel fs completion (local spill run) — the
"first kernel-scale field-sensitive run" headline; big-machine near-allyes
result; kernel-scale weld census under fs (container-summary implications).
DO NOT claim: incremental cross-iteration speedups (#15 bug open);
container summaries (redirected, unbuilt); anything from --cfl-sink-instr
as default (opt-in, reinterpreted as join denial).
