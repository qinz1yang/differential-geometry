/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Geometry.Metric.RiemannianMetricTensor
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

namespace DifferentialGeometry

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle

open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (n : WithTop ℕ∞)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

abbrev RiemannianMetric := Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)

def RiemannianMetric.to02Tensor {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    (g : RiemannianMetric I n M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (I := I) (M := M) (n := n) 2 :=
  Tensor.RSTensor.RiemannianMetricGen.to02TensorGen (I := I) (n := n) g

end
end DifferentialGeometry
