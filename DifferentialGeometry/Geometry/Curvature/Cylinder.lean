import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.Line
import DifferentialGeometry.Geometry.Metric.Cylinder

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Curvature

theorem ricciTensor_cylinderMetric
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) x) :
    ricciTensor (cylinderMetric g) x v w = ricciTensor g x.1 v.1 w.1 := by
  unfold cylinderMetric
  refine (ricciTensor_productMetric g _ x v w).trans ?_
  exact (congrArg (fun a : ℝ ↦ ricciTensor g x.1 v.1 w.1 + a)
    (ricciTensor_line_eq_zero _ x.2 v.2 w.2)).trans (add_zero _)

end DifferentialGeometry.Geometry.Curvature
