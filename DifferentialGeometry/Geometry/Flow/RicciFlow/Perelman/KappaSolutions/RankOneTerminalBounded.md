# RankOneTerminalBounded

`lem:ksol-rank-one-terminal-bounded` (`master05a.tex` L30065). Public:
`KLim.rankOne_terminal_scalar_bddAbove`.

## Assembly

Input: `hK : KLim kappa F`, `hdim : finrank ℝ E = 3`, and a
`TerminalSurfaceProduct (F.S.base.metric 0)` (the recorded output shape of
`lem:ksol-terminal-rank-one-product`).

1. `hjets` — `TerminalSurfaceJets.terminal_surface_factor_local_jets`.
2. `hg` — `P.complete`.
3. `hdim = 2` — `finrank_euclideanSpace_fin`; also used for the `NeZero` instance and to
   turn the `^ 2` of the noncollapse conclusion into `^ finrank ℝ (EuclideanSpace ℝ (Fin 2))`.
4. `hsec` — `P.positive.toNonnegative` through
   `Poincare.Geometry.hasNonnegativeSectionalCurvature_iff` and
   `metricRm04At_mem_tensor04SectionalNonnegativeCone_iff`.
5. `hnonneg` — private `metricScalarAt_nonneg_of_sectional_nonneg`: the trace over a
   `exists_gOrthonormalBasis` basis is a sum of sectional numerators
   (`metricScalarAt_eq_sum_sum_rm04_of_orthonormal`), so nonnegative sectional curvature
   gives nonnegative scalar curvature in any dimension — no two-dimensional identity needed.
6. `hnc` (`kappa/2`, all scales) — `universalCover_split_surface_tensor_half_noncollapsed`
   fed by private `klim_terminal_tensor_noncollapsed`, which reads `hK.noncollapsed` at the
   terminal `FlowTime ⟨0, _⟩` on the ball `⟨p, rho, hrho⟩` exactly as
   `UniversalCoverNoncollapse.universalCover_solution_slice_noncollapsed` does
   (`IsSpatiallyRmControlled` by `simpa [FlowMetricBall.rmNormSq, SolutionFamily.rm04,
   metricRm04_apply]`, then `.2` of `IsKappaNoncollapsed` with a `change`).
7. `static_surface_scalar_bddAbove_of_local_normalized_jets` gives
   `BddAbove (range (metricScalarAt P.h))`, and
   `TerminalProductScalar.bddAbove_scalar_iff_of_universalCover_product` descends it to
   `BddAbove (range (metricScalarAt (F.S.base.metric 0)))`, which is
   `BddAbove (range (F.S.scalar 0))` definitionally.

## Status

Conditional. Beyond the three new interfaces of `UpstreamProductCurvatureJets.lean`, the
endpoint inherits the lane's pre-existing admitted inputs through its consumers, in
particular `UpstreamRiemannianProduct` (order-zero product curvature and product volume),
`UpstreamCoverBallVolume`/`UpstreamVolumeNaturality` (covering ball image and volume),
`UpstreamCrossVolumeNaturality`, and `UpstreamLocalMetricCompactness` (local pointed metric
compactness) inside the static tail. `#print axioms` on
`KLim.rankOne_terminal_scalar_bddAbove` reports `[propext, sorryAx, Classical.choice,
Quot.sound]`; nothing here is claimed unconditional.

The `MeasurableSpace`/`BorelSpace` instances on `F.M` are the usual `borel` pair, matching
the ones baked into the consumed statements.

## Verification

`LEAN_NUM_THREADS=2 lake env lean` on the import-merged concatenation of the three new
files: 25.4 s, only the three interface `sorry` warnings. The module itself cannot be
checked in place until `UpstreamProductCurvatureJets` and `TerminalSurfaceJets` have
artifacts (no build was run by this task).
