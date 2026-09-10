import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Operator.Gradient.Basic

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Operator

namespace Poincare.Geometry.Metric

theorem metricSharp_difference_bound
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M]
    (g gRef : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (δ : ℝ) (hδ : δ < 1)
    (hsmall : metricDerivNorm (I := I) 0 g gRef gRef x ≤ δ) :
    let a := metricSharp gRef x α
    let d := metricSharp g x α - a
    Real.sqrt (gRef.inner x d d) ≤
      δ / (1 - δ) * Real.sqrt (gRef.inner x a a) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  dsimp only
  let a := metricSharp gRef x α
  let d := metricSharp g x α - a
  change Real.sqrt (gRef.inner x d d) ≤ δ / (1 - δ) * Real.sqrt (gRef.inner x a a)
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hsmall
  have hpos : 0 < 1 - δ := by linarith
  have hnn (v : TangentSpace I x) : 0 ≤ gRef.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (gRef.pos x v hv).le
  let D := Real.sqrt (gRef.inner x d d)
  let A := Real.sqrt (gRef.inner x a a)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hDs : D ^ 2 = gRef.inner x d d := Real.sq_sqrt (hnn d)
  have hbound (v w : TangentSpace I x) :
      |g.inner x v w - gRef.inner x v w| ≤
        δ * Real.sqrt (gRef.inner x v v) * Real.sqrt (gRef.inner x w w) := by
    apply (metricDifference_abs_le g gRef gRef x v w).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have heq : g.inner x d d = gRef.inner x a d - g.inner x a d := by
    change g.inner x (metricSharp g x α - a) d = _
    rw [map_sub (g.inner x), sub_apply, inner_metricSharp]
    rw [show gRef.inner x a d = α d from inner_metricSharp gRef x α d]
  have hu : g.inner x d d ≤ δ * A * D := by
    rw [heq]
    have h := (abs_le.mp (hbound a d)).1
    change -(δ * A * D) ≤ g.inner x a d - gRef.inner x a d at h
    linarith
  have hl : (1 - δ) * D ^ 2 ≤ g.inner x d d := by
    have h := (abs_le.mp (hbound d d)).1
    change -(δ * D * D) ≤ g.inner x d d - gRef.inner x d d at h
    rw [← hDs] at h
    nlinarith
  by_cases hzero : D = 0
  · change D ≤ δ / (1 - δ) * A
    rw [hzero]
    positivity
  · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hzero)
    have hlin : (1 - δ) * D ≤ δ * A := by
      apply (mul_le_mul_iff_of_pos_right hDpos).mp
      nlinarith [hl.trans hu]
    change D ≤ δ / (1 - δ) * A
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith

end Poincare.Geometry.Metric
