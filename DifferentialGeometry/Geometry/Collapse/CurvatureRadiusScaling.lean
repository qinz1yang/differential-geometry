import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private theorem sectionalBoundedBelowAt_scaled
    {g : SmoothRiemannianMetric I M} {K : ℝ} {x : M}
    (hsec : SectionalBoundedBelowAt g x K) (c : ℝ) (hc : 0 < c) :
    SectionalBoundedBelowAt (scaleMetric c hc g) x (K / c) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  intro v w
  simp only [scaleMetric_inner, metricRmStandard_scale c hc g x v w w v]
  have hcoefficient :
      K / c * (c * g.inner x v v * (c * g.inner x w w) - (c * g.inner x v w) ^ 2) =
        c * (K * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2)) := by
    field_simp [hc.ne']
  rw [hcoefficient]
  exact mul_le_mul_of_nonneg_left (hsec v w) hc.le

private theorem mul_curvatureRadius_le_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M) :
    ENNReal.ofReal (Real.sqrt c) * curvatureRadius g p ≤
      curvatureRadius (scaleMetric c hc g) p := by
  conv_lhs => rw [curvatureRadius]
  simp only [ENNReal.mul_iSup]
  refine iSup_le fun r => iSup_le fun hr => iSup_le fun hsec => ?_
  have hscaled : ∀ q ∈ riemannianBallOf (scaleMetric c hc g) p (Real.sqrt c * r),
      SectionalBoundedBelowAt (scaleMetric c hc g) q (-((Real.sqrt c * r) ^ 2)⁻¹) := by
    intro q hq
    rw [riemannianBallOf_scaleMetric c hc g p r] at hq
    have h := sectionalBoundedBelowAt_scaled (hsec q hq) c hc
    have hcoefficient : -(r ^ 2)⁻¹ / c = -((Real.sqrt c * r) ^ 2)⁻¹ := by
      rw [mul_pow, Real.sq_sqrt hc.le]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rwa [hcoefficient] at h
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  exact le_iSup_of_le (Real.sqrt c * r)
    (le_iSup_of_le (mul_pos (Real.sqrt_pos.mpr hc) hr)
      (le_iSup_of_le hscaled le_rfl))

theorem curvatureRadius_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M) :
    curvatureRadius (scaleMetric c hc g) p =
      ENNReal.ofReal (Real.sqrt c) * curvatureRadius g p := by
  apply le_antisymm ?_ (mul_curvatureRadius_le_scaleMetric g c hc p)
  have hback := mul_curvatureRadius_le_scaleMetric (scaleMetric c hc g)
    c⁻¹ (inv_pos.mpr hc) p
  have hinverse : scaleMetric c⁻¹ (inv_pos.mpr hc) (scaleMetric c hc g) = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [scaleMetric_inner, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  rw [hinverse] at hback
  have hfactors : ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (Real.sqrt c⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg c), Real.sqrt_inv,
      mul_inv_cancel₀ (Real.sqrt_pos.mpr hc).ne', ENNReal.ofReal_one]
  calc
    curvatureRadius (scaleMetric c hc g) p =
        (ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (Real.sqrt c⁻¹)) *
          curvatureRadius (scaleMetric c hc g) p := by rw [hfactors, one_mul]
    _ = ENNReal.ofReal (Real.sqrt c) *
        (ENNReal.ofReal (Real.sqrt c⁻¹) * curvatureRadius (scaleMetric c hc g) p) :=
      mul_assoc _ _ _
    _ ≤ ENNReal.ofReal (Real.sqrt c) * curvatureRadius g p :=
      mul_le_mul' le_rfl hback

theorem physical_curvatureRadius_eq_of_normalized
    (g : SmoothRiemannianMetric I M) (t : ℝ) (ht : 0 < t) (p : M) (r : ℝ)
    (hradius : curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht) g) p = ENNReal.ofReal r) :
    curvatureRadius g p = ENNReal.ofReal (Real.sqrt t * r) := by
  have hundo : scaleMetric t ht (scaleMetric t⁻¹ (inv_pos.mpr ht) g) = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [scaleMetric_inner, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  have h := curvatureRadius_scaleMetric (scaleMetric t⁻¹ (inv_pos.mpr ht) g) t ht p
  rw [hundo, hradius, ← ENNReal.ofReal_mul (Real.sqrt_nonneg t)] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
