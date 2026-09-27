import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.Riemannian.Basic

section

noncomputable section

open Bundle Manifold DifferentialGeometry Set
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def RiemannianMetricComplete [T3Space M] (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) : Prop :=
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  CompleteSpace M

end DifferentialGeometry.Geometry

end

end
