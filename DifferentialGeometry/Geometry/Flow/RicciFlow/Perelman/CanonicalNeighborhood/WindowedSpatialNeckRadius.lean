import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSpatialNeckTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckImageRadius
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_windowed_spatial_neck_transfer_threshold_of_strongNeck
    {alpha C1 C2 : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32)
    (hC1 : 0 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (delta kappa eps : ℝ) (x : M) (t : ℝ)
        (W : WindowedModelWitness delta kappa S x t),
        delta ≤ delta₀ →
        ∀ K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0,
        ∀ y ∈ K.domain.carrier,
        ∀ nk : StrongNeck W.model.S (neckModelTolerance alpha) y 0,
          ∃ nk' : SpatialNeck (S.base.metric t) (2 * alpha) (W.embedding y),
            nk'.map = partialDiffeomorphTransMixed nk.map W.embedding := by
  have hba : neckModelTolerance alpha < alpha :=
    (neckModelTolerance_le_smallness alpha).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ ha hsmall)
  obtain ⟨R, hRpos, hR⟩ := exists_uniform_neck_image_radius (neckModelTolerance_pos ha) hba
  obtain ⟨d, hdpos, hd⟩ := exists_windowed_spatial_neck_transfer_threshold
    ha (by linarith) hC1 hC2
  let B := 2 * C1 + R * Real.sqrt C2
  have hB : 0 < B + 1 := by dsimp only [B]; positivity
  let delta₀ := min ((B + 1)⁻¹ ^ 2) d
  refine ⟨delta₀, lt_min (sq_pos_of_pos (inv_pos.mpr hB)) hdpos, ?_⟩
  intro M _ _ _ _ _ D S delta kappa eps x t W hdelta K y hy nk
  have hdsq : delta ≤ (B + 1)⁻¹ ^ 2 := hdelta.trans (min_le_left _ _)
  have hdd : delta ≤ d := hdelta.trans (min_le_right _ _)
  have hbuffer : B ≤ modelRadius delta := by
    have hh := modelRadius_anti W.eps_pos hdsq
    have heq : modelRadius ((B + 1)⁻¹ ^ 2) = B + 1 := by
      rw [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hB.le), inv_inv]
    rw [heq] at hh
    linarith
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hqlo : C2⁻¹ ≤ W.model.S.scalar 0 y := by
    simpa only [hbase, mul_one] using (K.scalar_bounds y hy).1
  have hqinv : (W.model.S.scalar 0 y)⁻¹ ≤ C2 := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hC2pos) hqlo
  have hratio : R / Real.sqrt (W.model.S.scalar 0 y) ≤ R * Real.sqrt C2 := by
    simpa only [div_eq_mul_inv, Real.sqrt_inv] using
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqinv) hRpos.le
  have hr : K.radius ≤ C1 := by
    simpa only [hbase, Real.sqrt_one, div_one] using K.radius_upper
  have hcenter : riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y ≤
      ENNReal.ofReal (2 * C1) :=
    (K.inside_ball hy).le.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have houter : ∀ z ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹,
      nk.map z ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
        W.model.basepoint (modelRadius delta) := by
    intro z hz
    have hscale := riemannianClosedBallOf_scaleMetric (W.model.S.scalar 0 y) nk.Q_pos
      (W.model.S.base.metric 0) y (R / Real.sqrt (W.model.S.scalar 0 y))
    have hcancel : Real.sqrt (W.model.S.scalar 0 y) *
        (R / Real.sqrt (W.model.S.scalar 0 y)) = R := by
      have hsqrt : Real.sqrt (W.model.S.scalar 0 y) ≠ 0 :=
        (Real.sqrt_pos.mpr nk.Q_pos).ne'
      field_simp [hsqrt]
    rw [hcancel] at hscale
    have hn : nk.map z ∈ riemannianClosedBallOf
        (scaleMetric (W.model.S.scalar 0 y) nk.Q_pos (W.model.S.base.metric 0)) y R := by
      simpa only [riemannianClosedBallOf, mem_ofPred_eq, rescaledMetric, parabolicTime_zero] using
        hR W.model.M ancientTimeInterval W.model.S y 0 nk z hz
    rw [hscale] at hn
    have hnear : riemannianEDistOf (W.model.S.base.metric 0) y (nk.map z) ≤
        ENNReal.ofReal (R * Real.sqrt C2) :=
      hn.trans (ENNReal.ofReal_le_ofReal hratio)
    have hdist := (riemannianEDistOf_triangle (W.model.S.base.metric 0)
      W.model.basepoint y (nk.map z)).trans (add_le_add hcenter hnear)
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * C1)
      (by positivity : 0 ≤ R * Real.sqrt C2)] at hdist
    exact hdist.trans (ENNReal.ofReal_le_ofReal hbuffer)
  exact hd M D S delta kappa eps x t W hdd K y hy nk.toSpatialNeck houter

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
