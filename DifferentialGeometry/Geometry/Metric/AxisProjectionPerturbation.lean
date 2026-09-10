import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Laplacian

namespace DifferentialGeometry.Geometry.Metric

theorem axis_projection_difference_bound
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g gRef : SmoothRiemannianMetric I M) (x : M) (δ : ℝ) (hδ : δ < 1)
    (hmetric : metricDerivNorm 0 g gRef gRef x ≤ δ)
    (v : TangentSpace I x) (hv : gRef.inner x v v = 1) (z : TangentSpace I x) :
    let d := (g.inner x v z / g.inner x v v) • v - (gRef.inner x v z) • v
    Real.sqrt (gRef.inner x d d) ≤
      (2 * δ / (1 - δ)) * Real.sqrt (gRef.inner x z z) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hmetric
  let s := g.inner x v v
  let a := g.inner x v z
  let b := gRef.inner x v z
  let N := Real.sqrt (gRef.inner x z z)
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hdiff (w : TangentSpace I x) :
      |g.inner x v w - gRef.inner x v w| ≤ δ * Real.sqrt (gRef.inner x w w) := by
    have h := metricDifference_abs_le g gRef gRef x v w
    rw [hv, Real.sqrt_one, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right hmetric (Real.sqrt_nonneg _))
  have hs : |s - 1| ≤ δ := by
    have h := hdiff v
    rw [hv, Real.sqrt_one, mul_one] at h
    exact h
  have hs0 : 0 < s := by linarith [(abs_le.mp hs).1]
  have hsl : 1 - δ ≤ s := by linarith [(abs_le.mp hs).1]
  have hab : |a - b| ≤ δ * N := hdiff z
  have hb : |b| ≤ N := by
    have h := abs_metric_inner_le_sqrt_metric_quadratic gRef x v z
    rwa [hv, Real.sqrt_one, one_mul] at h
  have hnum : |a - s * b| ≤ 2 * δ * N := by
    calc
      _ = |(a - b) + (1 - s) * b| := congrArg abs (by ring)
      _ ≤ |a - b| + |(1 - s) * b| := abs_add_le _ _
      _ = |a - b| + |s - 1| * |b| := by rw [abs_mul, abs_sub_comm 1 s]
      _ ≤ δ * N + δ * N := add_le_add hab (mul_le_mul hs hb (abs_nonneg _) hδ0)
      _ = _ := by ring
  have hc : |a / s - b| ≤ (2 * δ / (1 - δ)) * N := by
    have heq : a / s - b = (a - s * b) / s := by field_simp
    rw [heq, abs_div, abs_of_pos hs0]
    apply (div_le_iff₀ hs0).mpr
    have hp : 0 ≤ (2 * δ / (1 - δ)) * N := by positivity
    have hm := mul_le_mul_of_nonneg_left hsl hp
    have he : (2 * δ / (1 - δ)) * N * (1 - δ) = 2 * δ * N := by
      rw [mul_right_comm, div_mul_cancel₀ _ (ne_of_gt (show 0 < 1 - δ by linarith))]
    exact hnum.trans (by rw [he] at hm; exact hm)
  dsimp only
  rw [← sub_smul, DifferentialGeometry.Geometry.Riemannian.sqrt_inner_smul,
    hv, Real.sqrt_one, mul_one]
  exact hc

end DifferentialGeometry.Geometry.Metric
