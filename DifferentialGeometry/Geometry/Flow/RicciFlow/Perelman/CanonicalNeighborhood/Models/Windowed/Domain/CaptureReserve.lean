import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessSpatialBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture


set_option autoImplicit false

noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


theorem modelRadius_sub_one_lt_captureRadius {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) :
    modelRadius eps - 1 < modelRadius eps * Real.sqrt (1 - eps) := by
  have hs : 0 < Real.sqrt eps := Real.sqrt_pos.mpr heps
  have hs1 : Real.sqrt eps < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt heps.le heps1
  have hsq : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt heps.le
  have ht : 0 ≤ Real.sqrt (1 - eps) := Real.sqrt_nonneg _
  have ht2 : Real.sqrt (1 - eps) ^ 2 = 1 - eps := Real.sq_sqrt (by linarith)
  have hstrict : 1 - Real.sqrt eps < Real.sqrt (1 - eps) := by
    nlinarith [mul_pos hs (sub_pos.mpr hs1)]
  have hmul := mul_lt_mul_of_pos_left hstrict (inv_pos.mpr hs)
  have hcancel : (Real.sqrt eps)⁻¹ * (1 - Real.sqrt eps) =
      (Real.sqrt eps)⁻¹ - 1 := by field_simp [hs.ne']
  simpa only [hcancel, modelRadius] using hmul

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D}


theorem WindowedModelWitness.exists_source_capture_reserve
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t) :
    ∃ eta : ℝ, 0 < eta ∧
      riemannianClosedBallOf (I := I3)
        (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x
        (modelRadius eps - 1 + eta) ⊆
          W.embedding '' riemannianClosedBallOf (I := I3)
            (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps) := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  let R := modelRadius eps
  let L := (Real.sqrt (1 - eps))⁻¹
  have hR : 0 < R := inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  have hroot : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr (by linarith [W.eps_lt_one])
  have hL : 0 < L := inv_pos.mpr hroot
  have hgap : R - 1 < R / L := by
    simpa only [R, L, div_inv_eq_mul] using
      modelRadius_sub_one_lt_captureRadius W.eps_pos W.eps_lt_one
  let eta := (R / L - (R - 1)) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hr : R - 1 + eta < R / L := by dsimp only [eta]; linarith
  have hsource : riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint R ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball
  have htime : (0 : ℝ) ∈ Icc (-modelDepth eps) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hlower : ∀ y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint R, ∀ v : TangentSpace I3 y,
      (W.model.S.base.metric 0).inner y v v ≤
        L ^ 2 * (rescaledMetric S t (S.scalar t x) W.scalar_pos 0).inner
          (W.embedding y) (mfderiv I3 I3 W.embedding y v)
          (mfderiv I3 I3 W.embedding y v) := by
    intro y hy v
    have hc := (W.comparison.equivalence 0 htime y hy v).1
    rw [W.comparison.pullback_eq 0 y hy (fun _ => v)] at hc
    have hfactor : L ^ 2 * (1 - eps) = 1 := by
      dsimp only [L]
      rw [inv_pow, Real.sq_sqrt (by linarith [W.eps_lt_one])]
      exact inv_mul_cancel₀ (by linarith [W.eps_lt_one])
    calc
      _ = L ^ 2 * ((1 - eps) * (W.model.S.base.metric 0).inner y v v) := by
        rw [← mul_assoc, hfactor, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (sq_nonneg L)
  refine ⟨eta, heta, ?_⟩
  have hcapture := closedBall_subset_image_of_metric_lower_crossModel
    (W.model.S.base.metric 0) (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
    W.embedding W.model.basepoint hR hL hr
    (RiemannianMetricComplete.closedEBall_isCompact hcomplete W.model.basepoint R)
    hsource hlower
  simpa only [W.base_map] using hcapture

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
