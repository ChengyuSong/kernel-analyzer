# Paper outline — ORCFL: Sound, Resource-Bounded Flows-To Call Graphs for the Linux Kernel

Status: draft outline (2026-08-06). Numbers cite the canonical pins and the
task log; items marked [PENDING] depend on runs still in flight.

## Title candidates

1. *Taming the Quotient: Sound Flows-To Call Graphs for the Linux Kernel on a
   Desktop*
2. *ORCFL: Answer-Anchored, Resource-Bounded Pointer Analysis for
   Multi-Million-Line Monolithic Systems*
3. *Where Indirect Calls Go: Anatomy and Surgery of a Kernel-Scale
   Flows-To Analysis*

## One-paragraph abstract (draft)

Resolving indirect calls soundly in the Linux kernel is the bottleneck for
kernel CFI, fuzzing harnesses, and reachability tooling; type-based
resolution over-approximates by an order of magnitude and is distrusted
under opaque pointers. We present ORCFL, an answer-anchored flows-to
analysis based on CFL reachability whose facts are (origin, field-shift)
pairs joined through witness-exact cluster unification. Three findings
shape the design. First, the dominant imprecision is a single may-alias
quotient class — the "giant" — which we show is born from
connected-component over-unification and sustained by fact accumulation
through a small set of semantically real rendezvous channels
(task_struct, tracepoint argument pools, allocator caches); the kernel's
object plane is otherwise bimodally modular (welds are 0.98% of merges).
Second, dispatch families whose function identity the quotient destroys
(tracepoints, static_call) are recoverable exactly at answer level from
census-complete binding tables, removing 32% of resolved pairs while
making the analysis faster. Third, field sensitivity need not be
all-or-nothing: gating exact field residues to nexus-typed origins
recovers 98% of full field sensitivity at a third of its cost, and
origin-batched solving — with copy-on-write process parallelism and
compressed plane spilling (600x, because quotient replication is
compressibility) — bounds memory to one batch's working set, enabling the
first kernel-scale field-sensitive run on a 62 GB desktop. Batched,
parallel, and spilled modes are byte-identical to the monolithic solve;
the staged-exactness arguments are machine-checked in Lean. On the 6.8
kernel, ORCFL resolves 18,189 indirect call sites to 5.69M pairs — 10.8x
tighter than type-based — in under 3 hours.

## Contributions (the reviewer-facing list)

C1. **Answer-anchored flows-to formulation.** Facts are (origin root, net
    field shift) pairs; memory aliasing is a join keyed by shared-origin
    witnesses; union-find clusters replace pairwise V saturation.
    Sound-by-construction; 10.8x tighter than type-based at kernel scale.
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
- Why sound indirect-call resolution matters (CFI policy size, fuzzing
  reachability, patch impact analysis); why type-based is both too loose
  (10.8x) and structurally untrustworthy under opaque pointers.
- The three walls: precision (the giant quotient), identity (dispatch
  families the quotient erases), resources (fs fact mass: 124B facts at
  kernel scale, 70x the kernel/ subset).
- Contributions bullet list (C1-C5/6).

### 2. Background and formulation (1.5 pp)
- CFL-reachability encoding (a/d/f edges), the P2 grammar, flows-to vs
  saturation; answer-anchored solving: mint origins, propagate
  (origin, shift) planes, join cells via witness clusters.
- The shift monoid + wildcard ⊤; Z_P residue bucketing as a monoid
  quotient. Soundness schema (Lean: FDeriv vs SolverClosure,
  origins_minted; the July minting bug as a violation caught by the model).

### 3. Anatomy: where imprecision lives (2 pp) — C3
- 3.1 The giant: 93% of pairs ride one class (fat-site census: 5.3M
  pairs, 6,138 sites); born vs sustained (presolve over-unification;
  fact accumulation forensics; diffuse entry).
- 3.2 Modularity thesis: coupler census, bimodal diversity histogram,
  welder taxonomy (couriers / honest neighbors / allocator); the
  presolve-cone lever (-201,724 free).
- 3.3 Nexus discovery: ptr-write subsystem diversity ranking; class A
  (intrusive links) vs class B (fat objects); what survives under fs
  (task rendezvous — semantically true flows).
- 3.4 Falsifications (table): fragmentation hypothesis, int-provenance
  residues, embedded-type hypothesis, emergent-scope pattern x3, born=
  exact. Each: claim, probe, honest-model verdict.

### 4. Identity channels (1.5 pp) — C2
- The principle + why graph-level attempts fail (tracepoint cells v1/v2
  autopsy: fn identity is a casualty of V-merge).
- Tracepoint keys: census-complete walker (trace_event_call /
  __bpf_raw_tp_map), completeness counters, kernel -1.50M/+0.
- Static_call ops tables: initializer inventory, table-authoritative vs
  type filter (return0), kernel -1.20M/+29-real.
- The INVOKE family (pair-correlated dispatch) as the earlier instance;
  design rule: identity lives at answer level until provenance cells
  exempt fn identity from the quotient.

### 5. Surgical field sensitivity (2 pp) — C4
- Why full fs walls: fragmentation without discrimination (facts
  replicate across a-connected fragments); cost model (floor + linear in
  exact roots).
- The gate: wildcard-minting = provable FI-equivalence per origin; fn@X
  free; containment closure via struct layout (and its null result).
- The decomposition table: default list / all / all+ids / fs13 with
  removals, share, time. Identity residues = 30% (the bpf_link_init
  shared-formal mechanism — ties back to the store-hub finding).
- Recall, not just precision: fs adds sound pairs (member->container
  composition), i.e., FI is not an over-approximation of fs answers.

### 6. Resource-bounded solving (2 pp) — C5
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

### 7. Evaluation (2.5 pp)
- E1 End-to-end: kernel 6.8 (2,618 objects), pin trajectory table:
  type-based -> flows-to v0 (14,799/5.1M) -> +summaries/invoke ->
  kernel-idchan (18,189/5.69M, 2.98 h, <45 GB). Sound micro suite +
  smoke gates.
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

### 8. Related work (1 p)
- From docs/novelty-and-related-work.md: BidirectedReach/POPL'18 (join
  layer rediscovered; witness-exact unification, shift residues,
  certificates new), Graspan (offload: their closure IS the output; our
  planes are derived — recompute vs spill trade), POCR/Pearl/GraCFL,
  MLTA/TypeDive, kernel CFI (KCFI, IFCC), unification vs inclusion
  hybrids (our presolve IS Steensgaard — and §3 quantifies exactly what
  that costs).

### 9. Conclusion (0.25 p)
- The quotient is not a bug to fix but a structure to understand: its
  irreducible core is the kernel's real rendezvous fabric; everything
  else yields to identity channels, surgical residues, and
  resource-bounded exact solving.

## Figures / tables shortlist

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
- If 10 pp: fold C6 into §3.4; cut §5 recall discussion to a paragraph;
  E5 comparisons to a table.
- Workshop/short fallback: §3 anatomy + §4 identity channels alone
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
