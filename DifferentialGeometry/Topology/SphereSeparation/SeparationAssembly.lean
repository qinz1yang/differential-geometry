import DifferentialGeometry.Topology.SphereSeparation.OpenThreeSpace
import DifferentialGeometry.Topology.SphereSeparation.HalfSpaceClosure

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphereSeparation

noncomputable def smoothSphereSidesOpenThreeSpaceOfAlexanderDualityCertificate
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD : HasAlexanderDualityH0Certificate (ψ ∘ e)) :
    SmoothSphereSides (Set.range e) := by
  let d := topologicalSphereSidesOpenThreeSpaceOfAlexanderDualityCertificate
    e he ψ hAD
  exact {
    toSphereSides := d
    compactClosureSmooth := compactSmoothSideClosure he d
    endClosureSmooth := endSmoothSideClosure he d
  }

theorem smoothSphereSides_side_sets_unique
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {S : Set N} (d₁ d₂ : SmoothSphereSides S) :
    d₁.compactSide = d₂.compactSide ∧ d₁.endSide = d₂.endSide :=
  SphereSides.side_sets_unique d₁.toSphereSides d₂.toSphereSides

end DifferentialGeometry.Topology.SphereSeparation
