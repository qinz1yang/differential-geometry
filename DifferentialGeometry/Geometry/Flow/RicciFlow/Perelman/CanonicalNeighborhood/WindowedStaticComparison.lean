import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticRescalingComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedScalarComparison
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompactGlobalization
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

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

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private theorem static_rescaling_weight_bound {K q c delta : ℝ} (hK : 1 ≤ K)
    (hq : K⁻¹ ≤ q) (hc0 : 0 ≤ c) (hc : c ≤ 2 * K) (hdelta : 0 ≤ delta)
    (hnear : |c - q| ≤ 243 * (1 + 3 * K) * delta) {a n : ℕ} (ha : a ≤ n) :
    Real.sqrt (q⁻¹ ^ (a + 2)) * c * delta + |c / q - 1| * Real.sqrt 3 ≤
      (2 * K * K ^ (n + 2) + 243 * (1 + 3 * K) * K * Real.sqrt 3) * delta := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hq0 : 0 < q := (inv_pos.mpr hK0).trans_le hq
  have hi : q⁻¹ ≤ K := by
    have hh := inv_anti₀ (inv_pos.mpr hK0) hq
    simpa only [inv_inv] using hh
  have hpow : q⁻¹ ^ (a + 2) ≤ K ^ (n + 2) :=
    (pow_le_pow_left₀ (inv_nonneg.mpr hq0.le) hi _).trans
      (pow_le_pow_right₀ hK (by omega))
  have hroot : Real.sqrt (q⁻¹ ^ (a + 2)) ≤ K ^ (n + 2) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨pow_nonneg hK0.le _, ?_⟩
    nlinarith [one_le_pow₀ hK (n := n + 2)]
  have hratio : |c / q - 1| ≤ 243 * (1 + 3 * K) * delta * K := by
    have heq : c / q - 1 = (c - q) * q⁻¹ := by field_simp
    rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hq0)]
    exact mul_le_mul hnear hi (inv_nonneg.mpr hq0.le) (by positivity)
  calc
    _ ≤ (K ^ (n + 2) * (2 * K)) * delta +
        (243 * (1 + 3 * K) * delta * K) * Real.sqrt 3 :=
      add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul hroot hc hc0 (by positivity)) hdelta)
        (mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg _))
    _ = _ := by ring

theorem WindowedModelWitness.exists_source_scalar_normalized_spatial_comparison_of_curvature_bounds
    {delta kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t) (hK : 1 ≤ K)
    (hsmall : 486 * K * (1 + 3 * K) * delta ≤ 1)
    {y : W.model.M}
    (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta))
    (hq : K⁻¹ ≤ W.model.S.scalar 0 y ∧ W.model.S.scalar 0 y ≤ K)
    (hrm : W.model.rmNormSq 0 y ≤ K ^ 2)
    (n : ℕ) (hn : n ≤ modelOrder delta) :
    ∃ hq0 : 0 < W.model.S.scalar 0 y, ∃ hR : 0 < S.scalar t (W.embedding y),
      |S.scalar t (W.embedding y) / (S.scalar t x * W.model.S.scalar 0 y) - 1| ≤
          243 * K * (1 + 3 * K) * delta ∧
      (2 * K)⁻¹ * S.scalar t x ≤ S.scalar t (W.embedding y) ∧
      S.scalar t (W.embedding y) ≤ (2 * K) * S.scalar t x ∧
      Nonempty (MetricComparisonOn
        (fun _ => scaleMetric (W.model.S.scalar 0 y) hq0 (W.model.S.base.metric 0))
        (fun _ => scaleMetric (S.scalar t (W.embedding y)) hR (S.base.metric t)) W.embedding
        (riemannianClosedBallOf (W.model.S.base.metric 0)
          W.model.basepoint (modelRadius delta)) {0} n
        ((2 * K * K ^ (n + 2) +
          243 * (1 + 3 * K) * K * Real.sqrt 3) * delta)) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hfactor : (4 : ℝ) ≤ K * (1 + 3 * K) := by
    nlinarith [sq_nonneg (K - 1)]
  have hscaled := mul_le_mul_of_nonneg_right hfactor W.eps_pos.le
  have hdelta : delta ≤ 1 / 4 := by nlinarith [hsmall]
  have hq0 : 0 < W.model.S.scalar 0 y := (inv_pos.mpr hK0).trans_le hq.1
  have ht0 : (0 : ℝ) ∈ Icc (-modelDepth delta) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hcomp := W.scalar_sub_le_of_model_curvature_bound hK0.le ht0 hy hrm
  let c := S.scalar t (W.embedding y) / S.scalar t x
  have hnorm : metricScalarAt (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
      (W.embedding y) = c := by
    simp only [rescaledMetric, parabolicTime, zero_div, add_zero, metricScalarAt_scaleMetric,
      SolutionOn.scalar, SolutionFamily.scalar]
    change (S.scalar t x)⁻¹ * S.scalar t (W.embedding y) = c
    dsimp only [c]
    rw [div_eq_mul_inv, mul_comm]
  rw [hnorm] at hcomp
  have hcoef := scalarComparisonC_le (n := 3) W.eps_pos.le hdelta
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hK0.le)
  norm_num only [Nat.cast_ofNat, Nat.cast_pow, Nat.cast_mul, Nat.cast_add] at hcoef
  have hnear : |c - W.model.S.scalar 0 y| ≤ 243 * (1 + 3 * K) * delta := by
    exact hcomp.trans (by nlinarith [hcoef])
  have hprod : 1 ≤ K * W.model.S.scalar 0 y := by
    have hh := mul_le_mul_of_nonneg_left hq.1 hK0.le
    rwa [mul_inv_cancel₀ hK0.ne'] at hh
  have hratio : |S.scalar t (W.embedding y) / (S.scalar t x * W.model.S.scalar 0 y) - 1| ≤
      243 * K * (1 + 3 * K) * delta := by
    have heq : S.scalar t (W.embedding y) / (S.scalar t x * W.model.S.scalar 0 y) - 1 =
        (c - W.model.S.scalar 0 y) / W.model.S.scalar 0 y := by
      dsimp only [c]
      field_simp [W.scalar_pos.ne', hq0.ne']
    rw [heq, abs_div, abs_of_pos hq0]
    apply (div_le_iff₀ hq0).mpr
    calc
      _ ≤ 243 * (1 + 3 * K) * delta := hnear
      _ ≤ (243 * (1 + 3 * K) * delta) * (K * W.model.S.scalar 0 y) :=
        le_mul_of_one_le_right (mul_nonneg (by positivity) W.eps_pos.le) hprod
      _ = _ := by ring
  have hden : 0 < S.scalar t x * W.model.S.scalar 0 y := mul_pos W.scalar_pos hq0
  have hhalf : |S.scalar t (W.embedding y) / (S.scalar t x * W.model.S.scalar 0 y) - 1| ≤
      1 / 2 := hratio.trans (by nlinarith [hsmall])
  have habs := abs_le.mp hhalf
  have hlo : (1 : ℝ) / 2 ≤ S.scalar t (W.embedding y) /
      (S.scalar t x * W.model.S.scalar 0 y) := by linarith
  have hhi : S.scalar t (W.embedding y) / (S.scalar t x * W.model.S.scalar 0 y) ≤ 2 := by
    linarith
  have hlower := (le_div_iff₀ hden).mp hlo
  have hupper := (div_le_iff₀ hden).mp hhi
  have hmodelLower := mul_le_mul_of_nonneg_left hq.1 W.scalar_pos.le
  have hmodelUpper := mul_le_mul_of_nonneg_left hq.2 W.scalar_pos.le
  have hinv : K⁻¹ = 2 * (2 * K)⁻¹ := by field_simp
  rw [hinv] at hmodelLower
  have hsource : (2 * K)⁻¹ * S.scalar t x ≤ S.scalar t (W.embedding y) ∧
      S.scalar t (W.embedding y) ≤ (2 * K) * S.scalar t x := by
    constructor <;> nlinarith
  have hR : 0 < S.scalar t (W.embedding y) :=
    (mul_pos (inv_pos.mpr (mul_pos (by norm_num) hK0)) W.scalar_pos).trans_le hsource.1
  have hc : 0 < c := div_pos hR W.scalar_pos
  have hcupper : c ≤ 2 * K := (div_le_iff₀ W.scalar_pos).mpr hsource.2
  let C := W.comparison.mono (subset_refl _) hn le_rfl
  let C' := C.staticRescale
    (delta := (2 * K * K ^ (n + 2) + 243 * (1 + 3 * K) * K * Real.sqrt 3) * delta)
    ht0 (W.model.S.scalar 0 y) c hq0 hc
    (mul_nonneg (by positivity) W.eps_pos.le) (fun a ha => by
      simpa only [show Module.finrank ℝ ThreeSpace = 3 from by simp [ThreeSpace],
        Nat.cast_ofNat] using static_rescaling_weight_bound hK
          hq.1 hc.le hcupper W.eps_pos.le hnear ha)
  have heq : scaleMetric c hc (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) =
      scaleMetric (S.scalar t (W.embedding y)) hR (S.base.metric t) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    simp only [scaleMetric_inner, rescaledMetric, parabolicTime, zero_div, add_zero]
    dsimp only [c]
    field_simp [W.scalar_pos.ne']
    exact mul_div_cancel_left₀ _ W.scalar_pos.ne'
  refine ⟨hq0, hR, hratio, hsource.1, hsource.2, ?_⟩
  rw [← heq]
  exact ⟨C'⟩


theorem WindowedModelWitness.exists_source_scalar_normalized_spatial_comparison
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hdelta : delta ≤ 1 / 4) (hbuffer : 2 * C1 ≤ modelRadius delta)
    (hsmall : 486 * C2 * (1 + 3 * C2) * delta ≤ 1)
    {y : W.model.M} (hy : y ∈ K.domain.carrier)
    (n : ℕ) (hn : n ≤ modelOrder delta) :
    ∃ hq : 0 < W.model.S.scalar 0 y, ∃ hR : 0 < S.scalar t (W.embedding y),
      Nonempty (MetricComparisonOn
        (fun _ => scaleMetric (W.model.S.scalar 0 y) hq (W.model.S.base.metric 0))
        (fun _ => scaleMetric (S.scalar t (W.embedding y)) hR (S.base.metric t)) W.embedding
        (riemannianClosedBallOf (W.model.S.base.metric 0)
          W.model.basepoint (modelRadius delta)) {0} n
        ((2 * C2 * C2 ^ (n + 2) +
          243 * (1 + 3 * C2) * C2 * Real.sqrt 3) * delta)) := by
  have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hq := K.scalar_bounds y hy
  rw [hbase, mul_one, mul_one] at hq
  have hrm : W.model.rmNormSq 0 y ≤ C2 ^ 2 := by
    have hb := K.rm_bound y hy
    rw [hbase, mul_one] at hb
    change Real.sqrt (W.model.rmNormSq 0 y) ≤ C2 at hb
    have heq := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg W.model 0 y)
    nlinarith [Real.sqrt_nonneg (W.model.rmNormSq 0 y)]
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  have hsource := W.scalar_bounds_on_canonical_domain K hdelta hbuffer hsmall hy
  have hR : 0 < S.scalar t (W.embedding y) :=
    (mul_pos (inv_pos.mpr (mul_pos (by norm_num) hC2)) W.scalar_pos).trans_le hsource.1
  obtain ⟨hq0, hR0, _, _, _, hcomparison⟩ :=
    W.exists_source_scalar_normalized_spatial_comparison_of_curvature_bounds
      K.one_le_comparison_constant hsmall
      (W.canonical_domain_subset_comparison_ball K hbuffer hy) hq hrm n hn
  exact ⟨hq0, hR, hcomparison⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem WindowedModelWitness.scalar_le_of_bounded_model
    {delta kappa K rho : ℝ} {x z : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t) (hK : 1 ≤ K)
    (hsmall : 486 * K * (1 + 3 * K) * delta ≤ 1)
    (hradius : rho ≤ modelRadius delta)
    (hmodel : ∀ y : W.model.M,
      y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho ∧
      K⁻¹ ≤ W.model.S.scalar 0 y ∧ W.model.S.scalar 0 y ≤ K ∧
      W.model.rmNormSq 0 y ≤ K ^ 2) :
    S.scalar t x ≤ (2 * K) * S.scalar t z := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcomplete : RiemannianMetricComplete (W.model.S.base.metric 0) :=
    ⟨W.model_ancient.complete 0 (by simp)⟩
  have hballcompact := hcomplete.closedEBall_isCompact W.model.basepoint rho
  have hcompact : IsCompact (univ : Set W.model.M) :=
    hballcompact.of_isClosed_subset isClosed_univ (fun y _ => (hmodel y).1)
  have hsource : W.embedding.source = univ := by
    apply eq_univ_of_forall
    intro y
    exact W.buffered_ball (riemannianClosedBallOf_mono _ _
      (hradius.trans (le_add_of_nonneg_right zero_le_one)) (hmodel y).1)
  have htarget : W.embedding.target = univ :=
    KappaSolutions.partialDiffeomorph_target_eq_univ_of_compact_source W.embedding
      (hsource.symm ▸ hcompact) ⟨W.model.basepoint, hsource.symm ▸ mem_univ _⟩
  let y := W.embedding.symm z
  have hy : y ∈ W.embedding.source := W.embedding.map_target (htarget.symm ▸ mem_univ z)
  have hyz : W.embedding y = z := W.embedding.right_inv (htarget.symm ▸ mem_univ z)
  obtain ⟨hq, hR, hratio, hlo, hhi, hcmp⟩ :=
    W.exists_source_scalar_normalized_spatial_comparison_of_curvature_bounds
      hK hsmall (riemannianClosedBallOf_mono _ _ hradius (hmodel y).1)
      ⟨(hmodel y).2.1, (hmodel y).2.2.1⟩ (hmodel y).2.2.2 0 (Nat.zero_le _)
  rw [hyz] at hlo
  have hmul := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2 * K)
  have hKpos : 0 < 2 * K := by linarith
  simpa only [← mul_assoc, mul_inv_cancel₀ hKpos.ne', one_mul] using hmul

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
