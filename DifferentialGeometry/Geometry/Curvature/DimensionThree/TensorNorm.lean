import DifferentialGeometry.Geometry.Curvature.Riemann.Tensor
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

def curvatureNormSq {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ M]
    (g : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (x : M)
    (A : DifferentialGeometry.Geometry.Curvature.Tensor04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := M) x) : ℝ :=
  DifferentialGeometry.Tensor0SBundle.normSq0S (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := M) g x 4 A

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
