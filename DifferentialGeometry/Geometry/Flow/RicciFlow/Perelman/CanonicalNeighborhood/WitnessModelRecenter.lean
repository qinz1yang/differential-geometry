import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessSpatialBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization


set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

section Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]


theorem eventually_scaled_closedBall_subset
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 ≤ R) {U : Set M} (hU : IsOpen U)
    (hsub : riemannianClosedBallOf g p R ⊆ U)
    (c : M → ℝ) (hc : ContinuousAt c p) (hcone : c p = 1) :
    ∀ᶠ z in 𝓝 p, ∃ hcz : 0 < c z,
      riemannianClosedBallOf (scaleMetric (c z) hcz g) z R ⊆ U := by
  obtain ⟨eta, heta, hroom⟩ :=
    exists_moving_riemannianClosedBall_subset g hcomplete p hR hU hsub
  have hcenter : ∀ᶠ z in 𝓝 p, z ∈ riemannianBallOf g p eta := by
    apply (isOpen_lt (continuous_riemannianEDist g p) continuous_const).mem_nhds
    change riemannianEDistOf g p p < ENNReal.ofReal eta
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr heta
  have hpositive : ∀ᶠ z in 𝓝 p, 0 < c z :=
    hc.eventually (Ioi_mem_nhds (by rw [hcone]; exact zero_lt_one))
  have hcontinuous : ContinuousAt (fun z => R / Real.sqrt (c z)) p :=
    continuousAt_const.div hc.sqrt (by rw [hcone, Real.sqrt_one]; exact one_ne_zero)
  have hradius : ∀ᶠ z in 𝓝 p, R / Real.sqrt (c z) < R + eta :=
    hcontinuous.eventually (Iio_mem_nhds (by
      change R / Real.sqrt (c p) < R + eta
      rw [hcone, Real.sqrt_one, div_one]
      linarith))
  filter_upwards [hcenter, hpositive, hradius] with z hz hcz hr
  refine ⟨hcz, ?_⟩
  have hscale := riemannianClosedBallOf_scaleMetric (c z) hcz g z
    (R / Real.sqrt (c z))
  have hcancel : Real.sqrt (c z) * (R / Real.sqrt (c z)) = R := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hcz)]
  rw [hcancel] at hscale
  rw [hscale]
  exact hroom z hz _ hr.le

end Metric

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D}

private local instance witnessRecenterC1 : IsManifold I3 1 M :=
  IsManifold.of_le (I := I3) (M := M) (n := ∞) (by decide)


theorem WindowedModelWitness.eventually_recentered_model
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t) :
    ∀ᶠ z in 𝓝 W.model.basepoint, ∃ hQ : 0 < W.model.S.scalar 0 z,
      let A := curvatureNormalizedFlow W.model W.model_ancient.carrier_eq
        W.model_ancient.regular_eq 0 (W.model.S.scalar 0 z) hQ
        (by change (0 : ℝ) ≤ 0; exact le_rfl) z
      IsAncientKappaSolution kappa A ∧ PointedFlowScalarAtBase A 1 ∧
        riemannianClosedBallOf (I := I3) (A.S.base.metric 0)
          A.basepoint (modelRadius eps + 1) ⊆ W.embedding.source := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hscalar : ContinuousAt (fun z => W.model.S.scalar 0 z) W.model.basepoint := by
    exact (metricScalar_smooth (W.model.S.base.metric 0)).continuous.continuousAt
  have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  filter_upwards [eventually_scaled_closedBall_subset (W.model.S.base.metric 0)
    hcomplete W.model.basepoint (by unfold modelRadius; positivity)
    W.embedding.open_source W.buffered_ball (fun z => W.model.S.scalar 0 z)
    hscalar hbase] with z hz
  obtain ⟨hQ, hball⟩ := hz
  refine ⟨hQ,
    isAncientKappaSolution_curvatureNormalizedFlow W.model W.model_ancient
      0 _ hQ (by change (0 : ℝ) ≤ 0; exact le_rfl) z rfl,
    curvatureNormalizedFlow_scalar_base W.model W.model_ancient.carrier_eq
      W.model_ancient.regular_eq 0 _ hQ
      (by change (0 : ℝ) ≤ 0; exact le_rfl) z rfl, ?_⟩
  change riemannianClosedBallOf (I := I3)
    (rescaledMetric W.model.S 0 (W.model.S.scalar 0 z) hQ 0) z
    (modelRadius eps + 1) ⊆ W.embedding.source
  simpa only [rescaledMetric, parabolicTime_zero] using hball


theorem WindowedModelWitness.eventually_recentered_model_at_source [T2Space M]
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t) :
    ∀ᶠ y in 𝓝 x, 0 < S.scalar t y ∧
      ∃ hQ : 0 < W.model.S.scalar 0 (W.embedding.symm y),
        let A := curvatureNormalizedFlow W.model W.model_ancient.carrier_eq
          W.model_ancient.regular_eq 0 (W.model.S.scalar 0 (W.embedding.symm y)) hQ
          (by change (0 : ℝ) ≤ 0; exact le_rfl) (W.embedding.symm y)
        IsAncientKappaSolution kappa A ∧ PointedFlowScalarAtBase A 1 ∧
          W.embedding A.basepoint = y ∧
          riemannianClosedBallOf (I := I3) (A.S.base.metric 0)
            A.basepoint (modelRadius eps + 1) ⊆ W.embedding.source := by
  have hp : W.model.basepoint ∈ W.embedding.source := by
    apply W.buffered_ball
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint W.model.basepoint ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hx : x ∈ W.embedding.target := by
    simpa only [W.base_map] using W.embedding.map_source' hp
  have hinv : W.embedding.symm x = W.model.basepoint := by
    exact (congrArg (W.embedding.symm : M → W.model.M) W.base_map.symm).trans
      (W.embedding.left_inv' hp)
  have hcontinuous := W.embedding.symm.contMDiffOn_toFun.continuousOn.continuousAt
    (W.embedding.open_target.mem_nhds hx)
  have htend : Tendsto (W.embedding.symm : M → W.model.M) (𝓝 x) (𝓝 W.model.basepoint) := by
    simpa only [hinv] using hcontinuous.tendsto
  have hsourcePositive : ∀ᶠ y in 𝓝 x, 0 < S.scalar t y :=
    (metricScalar_smooth (S.base.metric t)).continuous.continuousAt.eventually
      (Ioi_mem_nhds W.scalar_pos)
  filter_upwards [htend.eventually W.eventually_recentered_model,
    W.embedding.open_target.mem_nhds hx, hsourcePositive] with y hy hyt hpos
  obtain ⟨hQ, hancient, hscalar, hball⟩ := hy
  exact ⟨hpos, hQ, hancient, hscalar, W.embedding.right_inv' hyt, hball⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
