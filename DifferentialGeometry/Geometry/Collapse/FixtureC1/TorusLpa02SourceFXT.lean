import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusLpa02RegisterFXT
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterChain
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainStagesCutOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainZeroExit74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSmoothBases

/-!
# The torus source `S : ClosedChainEZRowsSource_RGC` with no empty input, and its stages
# (S-LPA02-TOR, G_last; closes D78-5 (3))

Lane S-LPA02-TOR (suffix `_FXT`). Over the CORRECTED register torus `torRegModelF_FXR R`
(periods `(N, N, min β₂ (w/4))`) at a register `R` of the threshold record
`T.withTorusV_FXT` (`lpa02V` enlarged, `TorusLpa02RegisterFXT`):

* `S.F = torRegClosedFamilyInstanceF_FXR …` with `witness := R.torRegLpa02Witness_FXT K`
  (LPA02's joint witness, proved) and the family / window / selection of S-FIX-REG2 G5b;
* `S.chain`: register V4's enhanced chain with (JA) on the corrected torus packet
  `torRegPacketsF_RHB` (the proof of `exists_torus_register_chainEJA_OFC`, whose chain producer
  `exists_chainEStrategy_RGC` quantifies over every packet at the register's values), at
  `ε_r = torErr_FXT ε₀`, `δ = torCone_FXT ε₀`, `Λ_z = T₀Low/20`.

* `exists_torus_source_FXT K`: strategy `T`, register `R`, `δ, ε_r, Λ_z` and the source `S`.
* **`torSource_closedStages_FXT K`** (consumer; the original goal of S-FIX-REG G3): the source
  `S` gives `S.bases74`, `S.smoothBases74`, `S.zsp02SmoothExit74 hεr` as TERMS, hence
  `closedStagesAt_OCL` (the revised stage-geometry record `ClosedStageGeometryU74` at `D_R`) and
  `cutAt_OCL` (the cut choice carried from `D_R`) on the flat torus chain.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle GC.MetricGeometry GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian GC.GraphManifold.Assembly.FC39P0
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **The torus source with no empty input**: a threshold record (below the combined strategy,
with `lpa02V` enlarged), a register at it, `δ, ε_r, Λ_z`, and the rows' source over the corrected
register torus. -/
theorem exists_torus_source_FXT (K : ℕ) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0} ∧
      ∃ (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (δ εr Λz : ℝ), εr ≤ 1 / 8 ∧
        Nonempty (ClosedChainEZRowsSource_RGC K R (torRegModelF_FXR R) δ εr Λz) := by
  obtain ⟨U', h2⟩ := exists_chainEStrategy_RGC K (closedStrategyCompleteV4C (earlyDataSharedV4 K))
  have hb := U'.withTorusCap_below_OFC
  have hbU := hb.trans_VAL6 h2.1.below_VAL6
  have hb' : ClosedStrategyBelowV4 U'.withTorusCap_OFC.withTorusV_FXT U' :=
    ClosedThresholdsV4.withTorusV_below_FXT hb
  have hT' : ClosedStrategyBelowV4 U'.withTorusCap_OFC.withTorusV_FXT
      (closedStrategyCompleteV4C (earlyDataSharedV4 K)) :=
    ClosedThresholdsV4.withTorusV_below_FXT hbU
  have hlc' : U'.withTorusCap_OFC.withTorusV_FXT.lc18 ≤ threeSplittingExclusionThreshold.{0, 0} :=
    U'.withTorusCap_lc18_OFC
  have R : ClosedRegisterV4 (earlyDataSharedV4 K) U'.withTorusCap_OFC.withTorusV_FXT :=
    Classical.choice (exists_closedRegisterV4 (earlyDataSharedV4 K) _)
  have hε0 := R.later.ε₀_pos
  have hεr0 : 0 ≤ torErr_FXT R.later.err.co.ε₀ := (torErr_pos_FXT hε0).le
  have hεr1 : torErr_FXT R.later.err.co.ε₀ < R.later.err.co.ε₀ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨U'.withTorusCap_OFC.withTorusV_FXT, hT', hlc', R, torCone_FXT R.later.err.co.ε₀,
    torErr_FXT R.later.err.co.ε₀, U'.withTorusCap_OFC.withTorusV_FXT.T₀Low R.stage R.later.circle
      R.later.excl R.later.err R.later.scale R.later.split.b R.later.split.β₁ / 20,
    min_le_right _ _, ?_⟩
  obtain ⟨C, -⟩ := h2.2 _ hb' R
    (torRegPacketsF_RHB R hT' hlc' K (torCone_FXT R.later.err.co.ε₀)
      (torErr_FXT R.later.err.co.ε₀) (U'.withTorusCap_OFC.withTorusV_FXT.T₀Low R.stage
        R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
        R.later.split.β₁ / 20)) hεr0 hεr1 (by linarith) (torPi_FXC1 _ 0)
  exact ⟨⟨torRegClosedFamilyInstanceF_FXR R hT' hlc' K (torCone_FXT R.later.err.co.ε₀)
    (torErr_FXT R.later.err.co.ε₀) _ (R.torRegLpa02Witness_FXT K), C⟩⟩

/-- **Consumer (the original goal of S-FIX-REG G3)**: on the flat torus chain,
`S.bases74`, `S.smoothBases74` and `S.zsp02SmoothExit74 hεr` are terms, so `closedStagesAt_OCL`
(the stage-geometry record at `D_R`) exists and its cut choice is `cutAt_OCL`. -/
theorem torSource_closedStages_FXT (K : ℕ) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      ∃ (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (δ εr Λz : ℝ)
        (S : ClosedChainEZRowsSource_RGC K R (torRegModelF_FXR R) δ εr Λz) (hεr : εr < 1 / 2)
        (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K))),
        Nonempty (ClosedStageGeometryU74 (S.goodCut_OCL S.bases74 hT hεr)
            (S.zsp02SmoothExit74 hεr)) ∧
          Nonempty (StageCutChoice74 (assembleStages74 (torRegModelF_FXR R)
            (S.zsp02SmoothExit74 hεr).rows (S.slimStage_OCL S.smoothBases74)
            (S.edgeStage74 S.smoothBases74) (S.circleStage_OCL S.smoothBases74))) := by
  obtain ⟨T, hT, -, R, δ, εr, Λz, hεr, ⟨S⟩⟩ := exists_torus_source_FXT K
  have hεr' : εr < 1 / 2 := by linarith
  exact ⟨T, hT, R, δ, εr, Λz, S, hεr', hT,
    ⟨S.closedStagesAt_OCL S.bases74 hT hεr' S.smoothBases74 (S.zsp02SmoothExit74 hεr')⟩,
    ⟨S.cutAt_OCL S.bases74 hT hεr' S.smoothBases74 (S.zsp02SmoothExit74 hεr').rows⟩⟩

end DifferentialGeometry.Geometry.Collapse
