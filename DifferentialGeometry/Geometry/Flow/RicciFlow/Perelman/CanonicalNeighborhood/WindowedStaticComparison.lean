import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticRescalingComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedScalarComparison

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
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hq := K.scalar_bounds y hy
  rw [hbase, mul_one, mul_one] at hq
  have hq0 : 0 < W.model.S.scalar 0 y := (inv_pos.mpr hC2).trans_le hq.1
  have hsource := W.scalar_bounds_on_canonical_domain K hdelta hbuffer hsmall hy
  have hR : 0 < S.scalar t (W.embedding y) :=
    (mul_pos (inv_pos.mpr (mul_pos (by norm_num) hC2)) W.scalar_pos).trans_le hsource.1
  let c := S.scalar t (W.embedding y) / S.scalar t x
  have hc : 0 < c := div_pos hR W.scalar_pos
  have hcupper : c ≤ 2 * C2 := (div_le_iff₀ W.scalar_pos).mpr hsource.2
  have hrm : W.model.rmNormSq 0 y ≤ C2 ^ 2 := by
    have hb := K.rm_bound y hy
    rw [hbase, mul_one] at hb
    change Real.sqrt (W.model.rmNormSq 0 y) ≤ C2 at hb
    have heq := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg W.model 0 y)
    nlinarith [Real.sqrt_nonneg (W.model.rmNormSq 0 y)]
  have ht0 : (0 : ℝ) ∈ Icc (-modelDepth delta) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hcomp := W.scalar_sub_le_of_model_curvature_bound hC2.le ht0
    (W.canonical_domain_subset_comparison_ball K hbuffer hy) hrm
  have hnorm : metricScalarAt (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
      (W.embedding y) = c := by
    simp only [rescaledMetric, parabolicTime, zero_div, add_zero, metricScalarAt_scaleMetric,
      SolutionOn.scalar, SolutionFamily.scalar]
    change (S.scalar t x)⁻¹ * S.scalar t (W.embedding y) = c
    dsimp only [c]
    rw [div_eq_mul_inv, mul_comm]
  rw [hnorm] at hcomp
  have hcoef := scalarComparisonC_le (n := 3) W.eps_pos.le hdelta
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hC2.le)
  norm_num only [Nat.cast_ofNat, Nat.cast_pow, Nat.cast_mul, Nat.cast_add] at hcoef
  have hnear : |c - W.model.S.scalar 0 y| ≤ 243 * (1 + 3 * C2) * delta := by
    exact hcomp.trans (by nlinarith [hcoef])
  let C := W.comparison.mono (subset_refl _) hn le_rfl
  let C' := C.staticRescale
    (delta := (2 * C2 * C2 ^ (n + 2) +
      243 * (1 + 3 * C2) * C2 * Real.sqrt 3) * delta)
    ht0 (W.model.S.scalar 0 y) c hq0 hc
    (mul_nonneg (by positivity) W.eps_pos.le) (fun a ha => by
      simpa only [show Module.finrank ℝ ThreeSpace = 3 from by simp [ThreeSpace],
        Nat.cast_ofNat] using static_rescaling_weight_bound K.one_le_comparison_constant
          hq.1 hc.le hcupper W.eps_pos.le hnear ha)
  have heq : scaleMetric c hc (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) =
      scaleMetric (S.scalar t (W.embedding y)) hR (S.base.metric t) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    simp only [scaleMetric_inner, rescaledMetric, parabolicTime, zero_div, add_zero]
    dsimp only [c]
    field_simp [W.scalar_pos.ne']
    exact mul_div_cancel_left₀ _ W.scalar_pos.ne'
  refine ⟨hq0, hR, ?_⟩
  rw [← heq]
  exact ⟨C'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
