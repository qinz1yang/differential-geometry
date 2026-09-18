import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture


set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Integral.Measure

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance sourceCurvatureC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem WindowedModelWitness.source_curvature_bound_at_of_model
    {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    {s : ℝ} (hs : s ∈ Icc (-modelDepth eps) 0) {y : W.model.M}
    (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps))
    (hrm : W.model.rmNormSq s y ≤ K ^ 2) :
    normSq0S (rescaledMetric S t (S.scalar t x) W.scalar_pos s) (W.embedding y) 4
      (metricRm04At (rescaledMetric S t (S.scalar t x) W.scalar_pos s) (W.embedding y)) ≤
      sourceCurvatureBound 3 K ^ 2 := by
  have hcomplete : RiemannianMetricComplete (W.model.S.base.metric 0) :=
    ⟨MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))⟩
  exact W.comparison.rmNormSq_le_on_closedBall (W.model.S.base.metric 0) hcomplete
    W.model.basepoint (inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)) W.eps_pos.le heps4
    (by have hh := five_le_modelOrder W.eps_pos heps4; omega) hK hs
    (W.buffered_ball (riemannianClosedBallOf_mono (W.model.S.base.metric 0)
      W.model.basepoint (le_add_of_nonneg_right zero_le_one) hy)) hy hrm


theorem WindowedModelWitness.source_curvature_bound_of_model
    {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2)
    {s : ℝ} (hs : s ∈ Icc (-(4 : ℝ)) 0) {z : M}
    (hz : z ∈ W.embedding ''
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2) :
    normSq0S (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z 4
      (metricRm04At (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z) ≤
      sourceCurvatureBound 3 K ^ 2 := by
  have hRtwo : 2 ≤ modelRadius eps := by
    have hh := modelRadius_anti W.eps_pos heps4
    rwa [modelRadius_quarter] at hh
  have hdepth : 4 ≤ modelDepth eps := by
    have hh := modelDepth_anti W.eps_pos heps4
    norm_num [modelDepth] at hh ⊢
    exact hh
  obtain ⟨y, hy, rfl⟩ := hz
  exact W.source_curvature_bound_at_of_model heps4 hK ⟨by linarith [hs.1], hs.2⟩
    (riemannianClosedBallOf_mono _ _ hRtwo hy) (hmodel s hs y hy)

theorem WindowedModelWitness.source_closedBall_compact_subset_image
    {eps kappa R r : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (p : W.model.M)
    (hR : 0 < R)
    (hBfull : riemannianClosedBallOf (W.model.S.base.metric 0) p R ⊆
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps))
    (hr : r < Real.sqrt (1 - eps) * R)
    {s : ℝ} (hs : s ∈ Icc (-modelDepth eps) 0) :
    IsCompact (riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos s) (W.embedding p) r) ∧
      riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos s) (W.embedding p) r ⊆
        W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) p R := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let B := riemannianClosedBallOf (W.model.S.base.metric 0) p R
  let ghat := rescaledMetric S t (S.scalar t x) W.scalar_pos
  have hgap : 0 < 1 - eps := sub_pos.mpr W.eps_lt_one
  have hroot : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr hgap
  have hL : 0 < (Real.sqrt (1 - eps))⁻¹ := inv_pos.mpr hroot
  have hr' : r < R / (Real.sqrt (1 - eps))⁻¹ := by
    simpa only [div_inv_eq_mul, mul_comm] using hr
  have hBcompact : IsCompact B := by
    apply RiemannianMetricComplete.closedEBall_isCompact
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hBsource : B ⊆ W.embedding.source :=
    hBfull.trans ((riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball)
  have hcapture : riemannianClosedBallOf (ghat s) (W.embedding p) r ⊆
      W.embedding '' B := by
    apply closedBall_subset_image_of_metric_lower (W.model.S.base.metric 0)
      (ghat s) W.embedding p (L := (Real.sqrt (1 - eps))⁻¹)
      hR hL hr' hBcompact hBsource
    intro y hy v
    have htime := ancientModel_metric_zero_le W.model W.model_ancient hs.2 y v
    have hlower := (W.comparison.equivalence s hs y (hBfull hy) v).1
    rw [W.comparison.pullback_eq s y (hBfull hy) (fun _ => v)] at hlower
    have hfactor : (Real.sqrt (1 - eps))⁻¹ ^ 2 * (1 - eps) = 1 := by
      rw [inv_pow, Real.sq_sqrt hgap.le, inv_mul_cancel₀ hgap.ne']
    calc
      _ ≤ (W.model.S.base.metric s).inner y v v := htime
      _ = (Real.sqrt (1 - eps))⁻¹ ^ 2 *
          ((1 - eps) * (W.model.S.base.metric s).inner y v v) := by
        rw [← mul_assoc, hfactor, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower (sq_nonneg _)
  have himageCompact : IsCompact (W.embedding '' B) := hBcompact.image_of_continuousOn
    (W.embedding.contMDiffOn_toFun.continuousOn.mono hBsource)
  exact ⟨himageCompact.of_isClosed_subset
    (isClosed_le (continuous_riemannianEDist (ghat s) (W.embedding p)) continuous_const) hcapture, hcapture⟩


theorem WindowedModelWitness.source_closedBall_compact_subset
    {eps kappa R r : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t)
    (hR : 0 < R) (hRfull : R ≤ modelRadius eps)
    (hr : r < Real.sqrt (1 - eps) * R)
    {s : ℝ} (hs : s ∈ Icc (-modelDepth eps) 0) :
    IsCompact (riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos s) x r) ∧
      riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos s) x r ⊆
        W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint R := by
  have h := W.source_closedBall_compact_subset_image W.model.basepoint hR
    (riemannianClosedBallOf_mono _ _ hRfull) hr hs
  simpa only [W.base_map] using h


theorem WindowedModelWitness.source_unitBall_compact_subset
    {eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4)
    {s : ℝ} (hs : s ∈ Icc (-(4 : ℝ)) 0) :
    IsCompact (riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos s) x 1) ∧
      riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos s) x 1 ⊆
        W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2 := by
  have hRtwo : 2 ≤ modelRadius eps := by
    have hh := modelRadius_anti W.eps_pos heps4
    rwa [modelRadius_quarter] at hh
  have hdepth : 4 ≤ modelDepth eps := by
    have hh := modelDepth_anti W.eps_pos heps4
    norm_num [modelDepth] at hh ⊢
    exact hh
  have hroot : (1 / 2 : ℝ) < Real.sqrt (1 - eps) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    linarith
  exact W.source_closedBall_compact_subset (by norm_num) hRtwo
    (by nlinarith) ⟨by linarith [hs.1], hs.2⟩


theorem WindowedModelWitness.closedBall_compact_curvature_bound
    {eps kappa K R r a b tau : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hR : 0 < R) (hRfull : R ≤ modelRadius eps)
    (hr : r < Real.sqrt (1 - eps) * R)
    (hwindow : Icc a b ⊆ Icc (-modelDepth eps) 0)
    (hmodel : ∀ s ∈ Icc a b, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint R,
        W.model.rmNormSq s y ≤ K ^ 2)
    (htau : tau ∈ Icc (-modelDepth eps) 0) :
    IsCompact (riemannianClosedBallOf
      (rescaledMetric S t (S.scalar t x) W.scalar_pos tau) x r) ∧
      ∀ s ∈ Icc a b, ∀ z ∈ riemannianClosedBallOf
        (rescaledMetric S t (S.scalar t x) W.scalar_pos tau) x r,
        normSq0S (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z 4
          (metricRm04At (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z) ≤
          sourceCurvatureBound 3 K ^ 2 := by
  obtain ⟨hcompact, hcapture⟩ :=
    W.source_closedBall_compact_subset hR hRfull hr htau
  refine ⟨hcompact, ?_⟩
  intro s hs z hz
  obtain ⟨y, hy, rfl⟩ := hcapture hz
  exact W.source_curvature_bound_at_of_model heps4 hK (hwindow hs)
    (riemannianClosedBallOf_mono _ _ hRfull hy) (hmodel s hs y hy)


theorem WindowedModelWitness.unitBall_compact_curvature_bound
    {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2)
    {a : ℝ} (ha : a ∈ Icc (-(4 : ℝ)) 0) :
    IsCompact (riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos a) x 1) ∧
      ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ z ∈
        riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos a) x 1,
        normSq0S (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z 4
          (metricRm04At (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z) ≤
          sourceCurvatureBound 3 K ^ 2 := by
  obtain ⟨hcompact, hcapture⟩ := W.source_unitBall_compact_subset heps4 ha
  exact ⟨hcompact, fun s hs z hz => W.source_curvature_bound_of_model heps4 hK hmodel hs (hcapture hz)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
