import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedStaticComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckImageRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedDistanceComparison

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

theorem exists_windowed_spatial_neck_transfer_threshold {alpha C1 C2 : ℝ}
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) (hC1 : 0 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (delta kappa eps : ℝ) (x : M) (t : ℝ)
        (W : WindowedModelWitness delta kappa S x t),
        delta ≤ delta₀ →
        ∀ K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0,
        ∀ y ∈ K.domain.carrier,
        ∀ nk : SpatialNeck (W.model.S.base.metric 0) (neckModelTolerance alpha) y,
          (∀ z ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹,
            nk.map z ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
              W.model.basepoint (modelRadius delta)) →
          ∃ nk' : SpatialNeck (S.base.metric t) (2 * alpha) (W.embedding y),
            nk'.map = partialDiffeomorphTransMixed nk.map W.embedding := by
  let n := ⌈(2 * alpha)⁻¹⌉₊
  let B := 2 * C2 * C2 ^ (n + 2) + 243 * (1 + 3 * C2) * C2 * Real.sqrt 3
  let F := 486 * C2 * (1 + 3 * C2)
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hB : 0 < B := by dsimp only [B]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  have hR : 0 < 2 * C1 + 1 := by positivity
  let delta₀ := min ((2 * C1 + 1)⁻¹ ^ 2)
    (min (2 * alpha) (min (1 / 4) (min F⁻¹ (neckSourceTolerance alpha / B))))
  have hd0 : 0 < delta₀ := lt_min (sq_pos_of_pos (inv_pos.mpr hR))
    (lt_min (by positivity) (lt_min (by norm_num)
      (lt_min (inv_pos.mpr hF) (div_pos (neckSourceTolerance_pos ha) hB))))
  refine ⟨delta₀, hd0, ?_⟩
  intro M _ _ _ _ _ D S delta kappa eps x t W hd K y hy nk houter
  have hdR : delta ≤ (2 * C1 + 1)⁻¹ ^ 2 := hd.trans (min_le_left _ _)
  have hdrest := hd.trans (min_le_right _ _)
  have hdalpha : delta ≤ 2 * alpha := hdrest.trans (min_le_left _ _)
  have hdrest' := hdrest.trans (min_le_right _ _)
  have hdquarter : delta ≤ 1 / 4 := hdrest'.trans (min_le_left _ _)
  have hdrest'' := hdrest'.trans (min_le_right _ _)
  have hdF : delta ≤ F⁻¹ := hdrest''.trans (min_le_left _ _)
  have hdB : delta ≤ neckSourceTolerance alpha / B := hdrest''.trans (min_le_right _ _)
  have hbuffer : 2 * C1 ≤ modelRadius delta := by
    have hh := modelRadius_anti W.eps_pos hdR
    have heq : modelRadius ((2 * C1 + 1)⁻¹ ^ 2) = 2 * C1 + 1 := by
      rw [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hR.le), inv_inv]
    rw [heq] at hh
    linarith
  have hord : n ≤ modelOrder delta := by
    have hh := Nat.ceil_le_ceil (inv_anti₀ W.eps_pos hdalpha)
    exact hh.trans (Nat.le_add_right _ 1)
  have hscalar : 486 * C2 * (1 + 3 * C2) * delta ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdF hF.le
    rw [mul_inv_cancel₀ hF.ne'] at hh
    exact hh
  have hbudget : B * delta ≤ neckSourceTolerance alpha := by
    have hh := (le_div_iff₀ hB).mp hdB
    simpa only [mul_comm] using hh
  obtain ⟨hq, hQ, ⟨C⟩⟩ := W.exists_source_scalar_normalized_spatial_comparison
    K hdquarter hbuffer hscalar hy n hord
  exact nk.exists_transport_of_local_comparisons hQ W.embedding C ha hsmall
    (mul_nonneg hB.le W.eps_pos.le) hbudget le_rfl rfl houter
    ((riemannianClosedBallOf_mono (W.model.S.base.metric 0) W.model.basepoint
      (by linarith : modelRadius delta ≤ modelRadius delta + 1)).trans W.buffered_ball)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_windowed_spatial_neck_center_transfer_threshold
    {alpha rho K : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32)
    (hrho : 0 ≤ rho) (hK : 1 ≤ K) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (delta kappa : ℝ) (x : M) (t : ℝ)
        (W : WindowedModelWitness delta kappa S x t),
        delta ≤ delta0 → ∀ y : W.model.M,
        y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho →
        K⁻¹ ≤ W.model.S.scalar 0 y → W.model.S.scalar 0 y ≤ K →
        W.model.rmNormSq 0 y ≤ K ^ 2 →
        ∀ nk : SpatialNeck (W.model.S.base.metric 0) (neckModelTolerance alpha) y,
          ∃ nk' : SpatialNeck (S.base.metric t) (2 * alpha) (W.embedding y),
            nk'.map = partialDiffeomorphTransMixed nk.map W.embedding ∧
            (2 * K)⁻¹ * S.scalar t x ≤ S.scalar t (W.embedding y) ∧
            S.scalar t (W.embedding y) ≤ (2 * K) * S.scalar t x ∧
            Real.sqrt (S.scalar t x) * metricDistance (S.base.metric t) x (W.embedding y) ≤
              2 * rho := by
  have hba : neckModelTolerance alpha < alpha :=
    (neckModelTolerance_le_smallness alpha).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ ha hsmall)
  obtain ⟨R, hR, hneck⟩ := exists_uniform_spatial_neck_image_radius
    (neckModelTolerance_pos ha) hba
  let n := ⌈(2 * alpha)⁻¹⌉₊
  let B := 2 * K * K ^ (n + 2) + 243 * (1 + 3 * K) * K * Real.sqrt 3
  let A := 486 * K * (1 + 3 * K)
  let L := max (rho + R * Real.sqrt K) (8 * rho) + 1
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  let delta0 := min (L⁻¹ ^ 2)
    (min (2 * alpha) (min (1 / 4) (min A⁻¹ (neckSourceTolerance alpha / B))))
  refine ⟨delta0, lt_min (sq_pos_of_pos (inv_pos.mpr hL))
    (lt_min (by positivity) (lt_min (by norm_num)
      (lt_min (inv_pos.mpr hA) (div_pos (neckSourceTolerance_pos ha) hB)))), ?_⟩
  intro M _ _ _ _ _ D S delta kappa x t W hd y hy hqlo hqhi hrm nk
  have hdL : delta ≤ L⁻¹ ^ 2 := hd.trans (min_le_left _ _)
  have hrest := hd.trans (min_le_right _ _)
  have hdalpha : delta ≤ 2 * alpha := hrest.trans (min_le_left _ _)
  have hrest' := hrest.trans (min_le_right _ _)
  have hdquarter : delta ≤ 1 / 4 := hrest'.trans (min_le_left _ _)
  have hrest'' := hrest'.trans (min_le_right _ _)
  have hdA : delta ≤ A⁻¹ := hrest''.trans (min_le_left _ _)
  have hdB : delta ≤ neckSourceTolerance alpha / B := hrest''.trans (min_le_right _ _)
  have hLbuffer : L ≤ modelRadius delta := by
    have hh := modelRadius_anti W.eps_pos hdL
    have heq : modelRadius (L⁻¹ ^ 2) = L := by
      rw [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hL.le), inv_inv]
    rwa [heq] at hh
  have houterbuffer : rho + R * Real.sqrt K ≤ modelRadius delta :=
    (le_trans (le_max_left _ _) (by dsimp [L]; linarith)).trans hLbuffer
  have hdistbuffer : 8 * rho ≤ modelRadius delta :=
    (le_trans (le_max_right _ _) (by dsimp [L]; linarith)).trans hLbuffer
  have hyrad : rho ≤ modelRadius delta := by nlinarith [houterbuffer, mul_nonneg hR.le (Real.sqrt_nonneg K)]
  have hynorm := riemannianClosedBallOf_mono _ _ hyrad hy
  have hn : n ≤ modelOrder delta :=
    (Nat.ceil_le_ceil (inv_anti₀ W.eps_pos hdalpha)).trans (Nat.le_add_right _ 1)
  have hscalar : 486 * K * (1 + 3 * K) * delta ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdA hA.le
    rwa [mul_inv_cancel₀ hA.ne'] at hh
  have hbudget : B * delta ≤ neckSourceTolerance alpha := by
    have hh := (le_div_iff₀ hB).mp hdB
    simpa only [mul_comm] using hh
  obtain ⟨hq, hQ, hratio, hlo, hhi, ⟨cmp⟩⟩ :=
    W.exists_source_scalar_normalized_spatial_comparison_of_curvature_bounds hK
      hscalar hynorm ⟨hqlo, hqhi⟩ hrm n hn
  have hqinv : (W.model.S.scalar 0 y)⁻¹ ≤ K := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hKpos) hqlo
  have hratioR : R / Real.sqrt (W.model.S.scalar 0 y) ≤ R * Real.sqrt K := by
    simpa only [div_eq_mul_inv, Real.sqrt_inv] using
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqinv) hR.le
  have houter : ∀ z ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹,
      nk.map z ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
        W.model.basepoint (modelRadius delta) := by
    intro z hz
    have hscale := riemannianClosedBallOf_scaleMetric (W.model.S.scalar 0 y) nk.Q_pos
      (W.model.S.base.metric 0) y (R / Real.sqrt (W.model.S.scalar 0 y))
    have hcancel : Real.sqrt (W.model.S.scalar 0 y) *
        (R / Real.sqrt (W.model.S.scalar 0 y)) = R := by
      field_simp [(Real.sqrt_pos.mpr nk.Q_pos).ne']
    rw [hcancel] at hscale
    have hn : nk.map z ∈ riemannianClosedBallOf
        (scaleMetric (W.model.S.scalar 0 y) nk.Q_pos (W.model.S.base.metric 0)) y R :=
      hneck W.model.M (W.model.S.base.metric 0) y nk z hz
    rw [hscale] at hn
    have hnear := hn.trans (ENNReal.ofReal_le_ofReal hratioR)
    have htri := (riemannianEDistOf_triangle (W.model.S.base.metric 0)
      W.model.basepoint y (nk.map z)).trans (add_le_add hy hnear)
    rw [← ENNReal.ofReal_add hrho (mul_nonneg hR.le (Real.sqrt_nonneg K))] at htri
    exact htri.trans (ENNReal.ofReal_le_ofReal houterbuffer)
  obtain ⟨nk', hmap⟩ := nk.exists_transport_of_local_comparisons hQ W.embedding cmp
    ha (by linarith) (mul_nonneg hB.le W.eps_pos.le) hbudget le_rfl rfl houter
    ((riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball)
  refine ⟨nk', hmap, hlo, hhi, ?_⟩
  have hp : W.model.basepoint ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint rho := by
    change riemannianEDistOf _ _ _ ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  have hdistance := (W.metricDistance_bounds_on_model_ball hdquarter hrho hdistbuffer
    W.model.basepoint hp y hy).2
  rw [W.base_map] at hdistance
  have hyreal : metricDistance (W.model.S.base.metric 0) W.model.basepoint y ≤ rho :=
    ENNReal.toReal_le_of_le_ofReal hrho hy
  have hsqrt : Real.sqrt (1 + delta) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> linarith
  exact hdistance.trans ((mul_le_mul hsqrt hyreal ENNReal.toReal_nonneg
    (by norm_num : (0 : ℝ) ≤ 2)))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
