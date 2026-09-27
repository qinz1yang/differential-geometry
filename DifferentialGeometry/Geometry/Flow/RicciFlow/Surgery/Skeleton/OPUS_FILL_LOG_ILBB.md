# Lane ILBB: brick 24b (positive-volume initial block) and the leaf `HistoryReducedVolumeInitialLowerBound`

Paths relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/` unless absolute. Scratch: session scratchpad `ilbb/`.

## 2026-09-26 findings (before any proof work)

### F1. L1 already exists on the collaborator branch `origin/codex/wt17-pc-build-warning` (Bennett Chow)
- `Surgery/Topology/HistoryAction/MinimumTime.lean` there (1871 lines, commit bd0be72d1 "Prove spatial action-minimum
  bounds along surgery histories") proves `ObservedHistory.exists_spatial_regularizedCost_minimum_lt_three_mul`:
  from a pole seed (`2aL₀ - 6a² < 0`, `T - a² ∈ Ioo (time first) (stageEndTime first)`), the regularity inputs
  `hregular` (every curve of action `< Abar` with admissible nodes has regular crossings) and `hbirthRegular`
  (a cheap spatial minimum at a birth time `T - k² = time i.succ` is regularly reached), and `3w < Abar`,
  it produces an attained spatial minimum `L < 3w` at `T - w²` in any target stage. This is exactly L1
  (`l_min ≤ 3/2` through surgeries), proved by per-stage Dini propagation plus event hand-off, with the
  interior upper support from the index estimate `sum_action_scalar_bound_of_spatial_minimum`
  (`Surgery/Topology/HistoryAction/Index.lean` there, 4682 lines, commit 01a76daf7).
- The same branch also has `Surgery/Topology/HistoryReducedMass.lean` (positive reduced mass on a PRIOR time window
  with a prior-window noncollapsing hypothesis; not the initial-time 24b, not directly usable for the leaf).
- Declaration closure of the L1 theorem over pc3 HEAD + CP2's relocated files (script `ilbb/need17.py`):
  ~9.6k lines in 20 modules (5 new modules: Index 4587, FiniteVariation 666, PrescribedEndpoints 459,
  SpatialMinimum 314, Continuity 59; the rest additions to 15 existing modules; 5 statement changes to handle by
  renamed copies). No `sorry`/`admit`/`nolint`/heartbeat options in those files.
- Decision: relocate (new untracked files, CP2 pattern) instead of re-deriving 4.6k lines of index estimates
  (AGENTS.md reuse rule). Proceeding.

### F2. The Λ question (lead, 2026-09-26)
- The frozen leaf does NOT supply `p₀.recenterConstant ≤ c` for any `c` fixed before `p₀`:
  `InCutoffClass` (`CanonicalNeighborhoodInduction.lean:165`) only gives `p₀.recenterConstant * δbound ≤ 1/2`, and
  `δbound` has no positive lower bound.
- It DOES supply everything the barrier chain uses the bound for. In the whole chain
  (`CapWindowActionRegularCrossing.lean`, ILBA's `CapWindowActionRegularCrossingBefore.lean`,
  `RegularMinimizerEndpointBarrier.lean`) the hypothesis `parameters.recenterConstant ≤ c` is threaded untouched and
  consumed only by `exists_uniform_static_cap_scale_lower_bound` (`GeometricCutoff.lean:614`), where it is used once,
  for `herror : p.recenterConstant * R.delta b ≤ 1/2`. From the leaf:
  `hasCanonicalCutoffRecords` gives `p.recenterConstant = p₀.recenterConstant` and `p.delta (time i.succ) ≤ δbound`,
  `R.delta_le` gives `R.delta b ≤ p.delta (time i.succ)`, and `InCutoffClass` gives `p₀.recenterConstant * δbound ≤ 1/2`;
  hence `herror` holds with no `Λ`.
- Plan: no interface edit. Add `exists_uniform_static_cap_scale_lower_bound_of_recenter_mul_le` (product premise) and
  copy the (short) consuming chain with the premise `∀ j, parameters.recenterConstant * parameters.delta (time j.succ) ≤ 1/2`
  in place of `parameters.recenterConstant ≤ c`.

## Status 2026-09-26 (afternoon)
- Relocation R17 (wt17 L1 closure, script `ilbb/gen17.py`, 20 files, scratch root `ILBBS.*` on subst drive `Q:` = `ilbb/`):
  generated; compiled clean so far up to `HistoryAction/AbsoluteContinuityStage` (fixes: copy referenced
  privates instead of `open private` (dot notation), fold stray `termination_by` chunks, CP2 providers imported).
  `HistoryAction/Index` (4.6k lines) next: instance-synthesis errors to fix (scope lines around its local instances).
- NEW `Surgery/Topology/CapWindowActionRegularCrossingRecenter.lean` (≈560 lines): the barrier chain in the product
  premise form (`∀ j, recenterConstant * delta (time j.succ) ≤ 1/2` in place of `recenterConstant ≤ c`), incl.
  `exists_uniform_static_cap_scale_lower_bound_of_recenterConstant_mul_delta_le`, node / initial-point / regular-crossing
  / regular-minimizer-endpoint versions (strict derivative cutoff as in ILBA). Compiles clean, 0 messages.
- NEW `Surgery/Topology/InitialEndpointPerturbation.lean` (L2): `exists_uniform_stage_zero_curvature_bound`,
  `exists_head_tail_split_of_mem_regularizedC1ActionValues`, `coe_stageRegularizedAction_mem_regularizedActionValues_stage_zero`,
  stage-zero metric/scalar comparison lemmas compile; main `regularizedCost_le_of_initial_tail_replacement` in progress
  (splitting to stay under the default heartbeat budget).

## Result (2026-09-26 15:10 local): L1, L2, 24b and the leaf proved; audit running

All files new and untracked, LF endings. Scratch compile = lean.exe, 4 threads, lakefile options, scratch roots
`ILBBS.*` (my files) / `ILBBC.*` (committed `Topology/HistoryPoleAction`, which has no olean in the shared build),
subst drive `Q:` = session scratchpad `ilbb/`; CP2's `CP2S/CP2C` and ILBA's `ILBA.G1/A24` oleans read-only.
Every file below compiles with 0 messages.

### Relocated from `origin/codex/wt17-pc-build-warning` (Bennett Chow; commits e033fb1f3 01a76daf7 bd0be72d1 and deps),
declaration closure of `ObservedHistory.exists_spatial_regularizedCost_minimum_lt_three_mul` (L1):
| File (under DifferentialGeometry/) | Kind | Lines |
|---|---|---|
| Analysis/Calculus/UpperSupport/Propagation | sibling of Monotonicity | 55 |
| Analysis/Integration/Integral/DominatedConvergenceQuadraticWeight | sibling of DominatedConvergence | 110 |
| Geometry/Connection/ParallelTransport/Naturality/PullbackLocalIsoDifferentiable | sibling of PullbackLocalIso | 301 |
| Geometry/Comparison/Variation/EndpointAccelerationSum | sibling of EndpointAccelerationGerm | 115 |
| Geometry/Comparison/Variation/Field/PrescribedEndpoints | added module | 486 |
| Geometry/Metric/Family/ChartCurvature/WithinSmoothnessScalar | sibling of WithinSmoothness | 83 |
| …/Perelman/LGeometry/Action/Minimizer/CarrierC1RegularityJointMetric | sibling of CarrierC1Regularity | 58 |
| …/Perelman/LGeometry/Action/Regularized/LagrangianRegularity | sibling of FirstVariation | 155 |
| …/Perelman/LGeometry/AdaptedField/ExistenceIcc | sibling of Existence | 821 |
| …/Perelman/LGeometry/Geodesic/SmoothTail | sibling of SmoothExtension | 148 |
| …/Perelman/LGeometry/Hamilton/TraceIntegralGeodesic | sibling of TraceIntegral | 81 |
| …/Perelman/LGeometry/Index/MinimizerNonnegativitySum | sibling of MinimizerNonnegativity | 100 |
| …/Perelman/LGeometry/Index/FiniteVariation | added module | 702 |
| …/Surgery/Topology/TerminalActionRegularity | sibling of TerminalAction | 264 |
| …/Surgery/Topology/HistoryAction/AbsoluteContinuityStage | sibling of AbsoluteContinuity | 846 |
| …/Surgery/Topology/HistoryAction/C1Attainment | sibling of Density | 122 |
| …/Surgery/Topology/HistoryAction/Continuity | added module (1 of 3 decls) | 80 |
| …/Surgery/Topology/HistoryAction/SpatialMinimum | added module | 335 |
| …/Surgery/Topology/HistoryAction/Index | added module (45+4 instances of 49) | 4686 |
| …/Surgery/Topology/HistoryAction/MinimumPropagation | sibling of MinimumTime | 1872 |
Relocation rules (script `ilbb/gen17.py`): exact wt17 scopes, only needed declarations (+ referenced privates copied,
+ instances of the same module), stray `termination_by` chunks folded into their owner, imports = original module +
wt17 imports present in pc3 + providers (relocated or CP2). Two statement clashes renamed (wt17 generalized them):
`covDerivAlong_map_localIso` → `covDerivAlong_map_localIso_of_mdifferentiableAt`,
`covDerivAlong_map_of_local_isometry_on` → `covDerivAlong_map_of_local_isometry_on_of_mdifferentiableAt`
(deferred merge: they generalize the committed ones, `MDifferentiableAt` in place of `ContMDiffAt ∞`).
`lRegularizedLagrangian_contDiffOn_two` is private in pc3's FirstVariation and public in wt17: relocated public
(`LagrangianRegularity`), name unique. Public-name clash scan against every .lean on disk: none.

### New mathematics (this lane)
| File | Content | Lines |
|---|---|---|
| Surgery/Topology/CapWindowActionRegularCrossingRecenter | barrier chain with the recenter budget premise (see F2) | 521 |
| Surgery/Topology/InitialSpatialMinimum | seed off event times; L1 at the initial time | 159 |
| Surgery/Topology/InitialEndpointPerturbation | L2: stage-zero curvature bound, head/tail split, tail replacement | 471 |
| Surgery/Topology/InitialRegularBlock | 24b, `reducedVolume_ge_of_initial_regular_block`, derivative glue, the leaf | 567 |

Headlines:
- `ObservedHistory.exists_uniform_initial_spatial_regularizedCost_minimum_lt_three_mul` (L1 at `v = √t`, target stage 0).
- `ObservedHistory.regularizedCost_le_of_initial_tail_replacement` (L2: cost(q) ≤ L + 2λ²(L + ...) + ... for
  `d_{g₀}(q₀,q) < ρ`, `ρ² ≤ (√T − √(T−θ))√T`, λ = exp(18Kθ)).
- `exists_uniform_initial_regular_block` (24b), `RetainedCoreHistory.reducedVolume_ge_of_initial_regular_block` (L3),
  `historyReducedVolumeInitialLowerBound_holds` (the leaf, unconditional, frozen leaf def unchanged).

### Statement deltas vs ANALYSIS_ILB (24b)
1. `p₀.recenterConstant ≤ Λ` (and the `Λ` binder) replaced by `p₀.recenterConstant * δbound ≤ 1/2` — the premise the
   frozen `InCutoffClass` supplies; no interface edit needed (F2).
2. `MeasurableSet U` strengthened to `IsOpen U` (U is a `g₀`-ball).
3. `InitialIdentification …` weakened to `Nonempty (InitialIdentification …)` (as ILBA; the leaf has `hH.1`).
4. The existential `a₀` also exports its defining property (fixed Hamilton–Ivey region and `R ≥ -3/a₀` for every
   identified history's initial metric); the leaf needs it for the stage floor `-(3/a₀)` of `reducedVolume`.
5. Constants: `C = Cmain/2`, `Cmain = 3 + 2e^{36Kθ₀}(3 + 2B/a₀·… ) + …` depends on `(g₀, B)` only; `κ₀ = κ_v c₁³`.

### Audit (scratch probe `ilbb/src/ILBBS/Test/Audit.lean`, not in the tree)
- 156 declarations of the 24 modules: axiom failures 0, findings of the 13 environment linters 0.
- Headlines `[propext, Classical.choice, Quot.sound]`: `historyReducedVolumeInitialLowerBound_holds`,
  `exists_uniform_initial_regular_block`, `RetainedCoreHistory.reducedVolume_ge_of_initial_regular_block`,
  `ObservedHistory.exists_uniform_initial_spatial_regularizedCost_minimum_lt_three_mul`,
  `ObservedHistory.regularizedCost_le_of_initial_tail_replacement`,
  `ObservedHistory.exists_spatial_regularizedCost_minimum_lt_three_mul`,
  `ObservedHistory.sum_action_scalar_bound_of_spatial_minimum`,
  `ObservedHistory.exists_uniform_regularCrossing_minimizer_of_regularizedCost_lt_of_recenter_budget`.
- Source scan: no sorry/admit/axiom/nolint/heartbeat/diagnostics/comments; only `set_option autoImplicit false`.

### Acceptance notes
- Needs CP2's 34 relocated files and ILBA's two files (`CapWindowActionRegularCrossingBefore`,
  `RegularMinimizerEndpointBarrier`) accepted first.
- The shared build has NO olean for the committed `Surgery/Topology/HistoryPoleAction` (scratch-built here as `ILBBC`);
  the acceptance build must build it.
- Root aggregate: register the 24 modules (dependency order): Propagation, DominatedConvergenceQuadraticWeight,
  PullbackLocalIsoDifferentiable, EndpointAccelerationSum, PrescribedEndpoints, WithinSmoothnessScalar,
  CarrierC1RegularityJointMetric, LagrangianRegularity, ExistenceIcc, SmoothTail, TraceIntegralGeodesic,
  MinimizerNonnegativitySum, FiniteVariation, TerminalActionRegularity, AbsoluteContinuityStage, C1Attainment,
  Continuity, SpatialMinimum, HistoryAction.Index, MinimumPropagation, CapWindowActionRegularCrossingRecenter,
  InitialEndpointPerturbation, InitialSpatialMinimum, InitialRegularBlock.
- Commit provenance for the relocated 20: origin/codex/wt17-pc-build-warning (Bennett Chow), declaration closure of
  `exists_spatial_regularizedCost_minimum_lt_three_mul` at 4c2e5c83b.
- Deferred merges: the two `_of_mdifferentiableAt` covDerivAlong lemmas generalize the committed ones; the
  `_of_recenter_budget` chain duplicates ILBA's `_of_derivative_before` chain with the weaker premise (ILBA's can
  become corollaries, `recenterConstant ≤ c` ⇒ budget for `δ ≤ 1/(2c)`); the relocated siblings follow CP2's pattern.

### Skeleton edit (Surgery/Skeleton/PoincareEndgame.lean)
Add `import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialRegularBlock` and replace
```
theorem historyReducedVolumeInitialLowerBound (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    HistoryReducedVolumeInitialLowerBound P₀ g₀ := by
  sorry
```
by
```
theorem historyReducedVolumeInitialLowerBound (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    HistoryReducedVolumeInitialLowerBound P₀ g₀ :=
  historyReducedVolumeInitialLowerBound_holds P₀ g₀
```
No change to `HistoryReducedVolumeInitialLowerBound` (no Λ needed).
