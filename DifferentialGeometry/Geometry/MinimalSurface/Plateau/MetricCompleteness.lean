import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import DifferentialGeometry.Topology.Connected.FiniteEDistance



noncomputable section

open Bundle Manifold DifferentialGeometry
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianMetricComplete_of_compact [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) : RiemannianMetricComplete g := by
  unfold RiemannianMetricComplete
  infer_instance

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_ne_top_of_preconnected [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x y : M) : riemannianEDistOf g x y ≠ ⊤ := by
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  exact DifferentialGeometry.Analysis.edist_ne_top_of_preconnected x y

end DifferentialGeometry.Geometry
