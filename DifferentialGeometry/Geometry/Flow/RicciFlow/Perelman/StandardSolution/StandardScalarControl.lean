import DifferentialGeometry.Geometry.Curvature.ScalarControlsRm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureOperator

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.normSq_rm_le_scalar_sq
    (S : PartialStandardSolution) (t : ℝ) (ht : t ∈ S.domain) (x : E3) :
    normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x) ≤
      100 ^ 2 * (metricScalarAt (S.metric t) x) ^ 2 := by
  exact DifferentialGeometry.Geometry.Curvature.normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
    (S.metric t) x (by simp) (S.curvatureOperator_nonnegative t ht x)

end DifferentialGeometry.PDE.RicciFlow

end
