import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Mathlib.LinearAlgebra.Basis.SMul

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem orthonormalBasisAt_scaleMetric
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (b : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hb : OrthonormalBasisAt g x b) :
    OrthonormalBasisAt (scaleMetric c hc g) x
      (b.isUnitSMul (fun _ : Fin 3 => isUnit_iff_ne_zero.mpr
        (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hc))))) := by
  intro i j
  rw [Module.Basis.isUnitSMul_apply, Module.Basis.isUnitSMul_apply,
    scaleMetric_inner_inv_sqrt_smul]
  exact hb i j

private theorem curvatureOperatorMatrixAt_scaleMetric
    [T2Space M]
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (b : Module.Basis (Fin 3) ℝ (TangentSpace I x)) :
    curvatureOperatorMatrixAt x
      (b.isUnitSMul (fun _ : Fin 3 => isUnit_iff_ne_zero.mpr
        (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hc)))))
      (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) =
      c⁻¹ • curvatureOperatorMatrixAt x b (metricAlgebraicCurvatureTensorAt g x) := by
  ext i j
  simp only [curvatureOperatorMatrixAt, Module.Basis.isUnitSMul_apply,
    tensor04StandardAt]
  have hv := metricRm04At_scaleMetric_inv_sqrt_smul c hc g x
    (vec4 (b (bivectorIndex3 i).1) (b (bivectorIndex3 i).2)
      (b (bivectorIndex3 j).2) (b (bivectorIndex3 j).1))
  convert hv using 1 <;> congr 1
  ext k
  fin_cases k <;> rfl

theorem metricCurvatureOperatorRankAt_scaleMetric
    [T2Space M]
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) :
    metricCurvatureOperatorRankAt (scaleMetric c hc g) x hdim =
      metricCurvatureOperatorRankAt g x hdim := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨b, hb⟩ := exists_orthonormalBasisAt g x hdim
  rw [metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal
    (scaleMetric c hc g) x hdim _ (orthonormalBasisAt_scaleMetric c hc g x b hb),
    curvatureOperatorMatrixAt_scaleMetric,
    Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero hc.ne')),
    ← metricCurvatureOperatorRankAt_eq_matrix_rank_of_orthonormal g x hdim b hb]

end DifferentialGeometry.Geometry.Curvature.DimensionThree

end
