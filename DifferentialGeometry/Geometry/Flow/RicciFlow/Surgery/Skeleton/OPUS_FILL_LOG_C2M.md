# OPUS fill log C2M — bricks M1, M3, M (DESIGN_C2_ASSEMBLY §5.2)

Worktree `D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf` @ 9126abc30. Append-only.

## Start (2026-09-26)

Read AGENTS.md, NAMING.md §2–6, DESIGN_C2_ASSEMBLY §1(a), §2, §5.2, H2/H3 digest, MinDomain,
Exponential, ExponentialSmooth, ExponentialFamily, AbsoluteContinuity.

Plan:
- M1 `upperSemicontinuous_regularizedCost`: ε-optimal competitor, cutoff chart perturbation of
  the stage-`first` tail near `v` (nodes and base fixed), dominated convergence with `L²` chart
  velocity from finite action + floor + chart comparison of the metric.
- L continuity on `historyLExpOpenDomain`: local window families at every `s ∈ [0, v]`
  (interior: `exists_contMDiffOn_window_family_historyLCurve`; end: the `hasPrefixFamily_end`
  family; base: `lRegularizedFamily_extend`), dominated convergence per piece.
- M3 on the open domain: pieces locally C¹ near every point of their closed interval.
- M (interior end `T - v² ∈ Ioo`): `K = U \ {Z ∈ U | cost (f Z) < L Z}`, open minus open.

## Progress 1 (16:31 UTC) — M1 proved

New file `Surgery/Topology/HistoryLGeometry/CostSemicontinuity.lean` (compiles, 0 errors, 0 warnings):
- single-flow `Perelman.eventually_exists_lRegularizedAction_lt_of_absolutelyContinuousOnInterval`
  (AC curve on `[a,b]`, integrable Lagrangian, carrier on `Ioc a b`, action `< L` ⇒ near `γ b`
  every endpoint has an AC competitor with same start, integrable Lagrangian and action `< L`);
  proof: smoothTransition cutoff chart perturbation `e.symm (e∘γ + φ•w)` on `[c,b]`, dominated
  convergence with bound `|Λ|(‖u'‖² + C) + 2s²|C_R|`, `‖u'‖² ∈ L¹` from the positive chart
  quadratic lower bound.
- `ObservedHistory.upperSemicontinuous_regularizedCost` (hypotheses `hv`, `hfloor` only: the
  design's `hT`, `hend` are unused — both come from the competitor — so dropped).
- axioms: [propext, Classical.choice, Quot.sound].

## Progress 2 (17:25 UTC) — M3 on the open domain

New file `Surgery/Topology/HistoryLGeometry/CurveAction.lean` (compiles, 0 errors, 0 warnings):
`absolutelyContinuousOnInterval_historyLCurve_of_mem_historyLExpOpenDomain`,
`intervalIntegrable_stageRegularizedLagrangian_historyLCurve_of_mem_historyLExpOpenDomain`,
`regularizedExtendedAction_historyLCurve_eq_historyLAction_of_mem_historyLExpOpenDomain`.
Route: per-point window representation (base: initial-vector window's `lRegularizedCurve`;
interior: `IsHistoryLGeodesicOn` windows; end: the open-domain window past `v`), local AC +
local Lagrangian bound, compactness. The whole-domain M3 (closed start or no window past `v`)
needs the E2a velocity limit at `v` (E lane); not duplicated here.
Note: the lead's `lake build` in pc3 transiently deletes oleans; compiles of files importing
uncommitted new modules use the scratch pattern (`sroot/C2MScratch`, `lean --root -o`).
Next: `MinDomainMeasurable.lean` — L lower semicontinuous on the open domain by Fatou (only
pointwise continuity at interior parameters from `exists_contMDiffOn_window_family_historyLCurve`),
then `K = U \ {cost∘f < L}`.

## Progress 3 (18:01 UTC) — M1, M3, M proved unconditionally (design statements)

E's package landed at 2c47e2482 (`ExponentialClosedStart.lean`, `ClosedStartVelocity.lean`), so
the closed-start case is done now, not deferred.
- `CostSemicontinuity.lean`: + single-flow
  `exists_absolutelyContinuousOnInterval_of_lRegularizedSpeedSq_le` (bounded speed near the
  end ⇒ AC up to the end and bounded Lagrangian; chart Lipschitz via the chart-quadratic lower bound).
- `CurveAction.lean` (now whole domain, design names): `absolutelyContinuousOnInterval_historyLCurve`,
  `intervalIntegrable_stageRegularizedLagrangian_historyLCurve`,
  `regularizedExtendedAction_historyLCurve_eq_historyLAction_of_mem`. End case for every `Z`:
  stage slab `exists_incomingSlab_stageMetric`, stage geodesic via E's private
  `isLRegularizedGeodesicOn_stage_of_isHistoryLGeodesicOn`, speed bound via the private
  `exists_lRegularizedSpeedSq_le_of_closedStart` (artificial start `a := T - v²`).
- `MinDomainMeasurable.lean`: `measurableSet_historyMinDomain` (hv, hT ∈ Ico, hfloor — design
  statement; from E's `exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain`) and
  `measurableSet_historyMinDomain_of_mem_Ioo` (hv, hend ∈ Ioo, hfloor; no hT; L l.s.c. by Fatou).
  Internal private `measurableSet_historyMinDomain_of_isOpen` takes the open-set package.
- Scratch compile (lake env lean, lakefile options) of all three: 0 errors, 0 warnings; `#lint`
  clean; axioms [propext, Classical.choice, Quot.sound] for all public headlines.
- Not done (outside brief): registration in `DifferentialGeometry.lean`, `lake build`, commit.
