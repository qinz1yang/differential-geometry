import DifferentialGeometry.Geometry.Metric.SharpCovectorPerturbation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

noncomputable section
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Geometry.Curvature

theorem ricciSharp_difference_bound_of_tensor_difference
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g gRef : SmoothRiemannianMetric I M) (x : M) (δ ρ : ℝ) (hδ : δ < 1)
    (hmetric : metricDerivNorm (I := I) 0 g gRef gRef x ≤ δ)
    (hRicci : Real.sqrt (normSq0S (I := I) gRef x 2
      (metricRicci g x - metricRicci gRef x)) ≤ ρ) (v : TangentSpace I x) :
    let b := ricciSharp gRef x v
    let d := ricciSharp g x v - b
    Real.sqrt (gRef.inner x d d) ≤
      (ρ * Real.sqrt (gRef.inner x v v) + δ * Real.sqrt (gRef.inner x b b)) / (1 - δ) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hρ : 0 ≤ ρ := (Real.sqrt_nonneg _).trans hRicci
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis gRef x
  have hcov (w : TangentSpace I x) :
      |ricciTensor g x v w - ricciTensor gRef x v w| ≤
        (ρ * Real.sqrt (gRef.inner x v v)) * Real.sqrt (gRef.inner x w w) := by
    have h := abs_apply_le_sqrt_normSq0S (I := I) gRef x 2 basis hON
      (metricRicci g x - metricRicci gRef x) (vec2 v w)
    have heq : (metricRicci g x - metricRicci gRef x) (vec2 v w) =
        ricciTensor g x v w - ricciTensor gRef x v w := by
      rw [Tensor0SSpace.sub_apply]
      change metricRicciAt g x (vec2 v w) - metricRicciAt gRef x (vec2 v w) = _
      rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    rw [heq, Fin.prod_univ_two] at h
    simp only [vec2, Fin.isValue, if_true] at h
    exact h.trans (by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hRicci (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  exact DifferentialGeometry.Geometry.Metric.metricSharp_difference_bound_of_covector_difference
    g gRef x (ricciTensor g x v).toLinearMap (ricciTensor gRef x v).toLinearMap
    δ (ρ * Real.sqrt (gRef.inner x v v)) hδ (mul_nonneg hρ (Real.sqrt_nonneg _))
    hmetric hcov

end DifferentialGeometry.Geometry.Curvature
