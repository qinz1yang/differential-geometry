import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Operator.Gradient.Basic

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Metric

theorem metricSharp_difference_bound_of_covector_difference
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g gRef : SmoothRiemannianMetric I M) (x : M)
    (α β : TangentSpace I x →ₗ[ℝ] ℝ) (δ η : ℝ) (hδ : δ < 1) (hη : 0 ≤ η)
    (hmetric : metricDerivNorm (I := I) 0 g gRef gRef x ≤ δ)
    (hcovector : ∀ v : TangentSpace I x,
      |α v - β v| ≤ η * Real.sqrt (gRef.inner x v v)) :
    let b := metricSharp gRef x β
    let d := metricSharp g x α - b
    Real.sqrt (gRef.inner x d d) ≤
      (η + δ * Real.sqrt (gRef.inner x b b)) / (1 - δ) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  dsimp only
  let b := metricSharp gRef x β
  let d := metricSharp g x α - b
  let D := Real.sqrt (gRef.inner x d d)
  let B := Real.sqrt (gRef.inner x b b)
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hmetric
  have hpos : 0 < 1 - δ := by linarith
  have hnn (v : TangentSpace I x) : 0 ≤ gRef.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (gRef.pos x v hv).le
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hDs : D ^ 2 = gRef.inner x d d := Real.sq_sqrt (hnn d)
  have hbound (v w : TangentSpace I x) :
      |g.inner x v w - gRef.inner x v w| ≤
        δ * Real.sqrt (gRef.inner x v v) * Real.sqrt (gRef.inner x w w) := by
    apply (metricDifference_abs_le g gRef gRef x v w).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmetric (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have heq : g.inner x d d = α d - β d + gRef.inner x b d - g.inner x b d := by
    change g.inner x (metricSharp g x α - b) d = _
    rw [map_sub (g.inner x), sub_apply, inner_metricSharp]
    rw [show gRef.inner x b d = β d from inner_metricSharp gRef x β d]
    ring
  have hu : g.inner x d d ≤ (η + δ * B) * D := by
    rw [heq]
    have hm := (abs_le.mp (hbound b d)).1
    have hc := (abs_le.mp (hcovector d)).2
    change -(δ * B * D) ≤ g.inner x b d - gRef.inner x b d at hm
    change α d - β d ≤ η * D at hc
    nlinarith
  have hl : (1 - δ) * D ^ 2 ≤ g.inner x d d := by
    have h := (abs_le.mp (hbound d d)).1
    change -(δ * D * D) ≤ g.inner x d d - gRef.inner x d d at h
    rw [← hDs] at h
    nlinarith
  change D ≤ (η + δ * B) / (1 - δ)
  by_cases hz : D = 0
  · rw [hz]
    positivity
  · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hz)
    have he : (1 - δ) * D ≤ η + δ * B := by
      apply (mul_le_mul_iff_of_pos_right hDpos).mp
      nlinarith [hl.trans hu]
    rw [le_div_iff₀ hpos]
    nlinarith

end DifferentialGeometry.Geometry.Metric
