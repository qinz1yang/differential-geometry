import DifferentialGeometry.Topology.SphereSeparation.Nesting
import DifferentialGeometry.Topology.SphereSeparation.OpenThreeSpace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace Poincare.Topology.SphereSeparation

theorem disjoint_spheres_nested_openThreeSpace_of_alexanderDuality
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (e₁ e₂ : SphereTwo → N)
    (he₁ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e₁)
    (he₂ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e₂)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD₁ : HasAlexanderDualityH0Certificate (ψ ∘ e₁))
    (hAD₂ : HasAlexanderDualityH0Certificate (ψ ∘ e₂))
    (hdisjoint : Disjoint (Set.range e₁) (Set.range e₂))
    (hmeet :
      let d₁ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
        e₁ he₁ ψ hAD₁
      let d₂ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
        e₂ he₂ ψ hAD₂
      (d₁.compactSide ∩ d₂.compactSide).Nonempty) :
    let d₁ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
      e₁ he₁ ψ hAD₁
    let d₂ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
      e₂ he₂ ψ hAD₂
    Xor
      (closure d₁.compactSide ⊂ d₂.compactSide ∧
        d₂.compactSide = interior (closure d₂.compactSide) ∧
        closure d₁.compactSide ⊂ closure d₂.compactSide)
      (closure d₂.compactSide ⊂ d₁.compactSide ∧
        d₁.compactSide = interior (closure d₁.compactSide) ∧
        closure d₂.compactSide ⊂ closure d₁.compactSide) := by
  let d₁ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
    e₁ he₁ ψ hAD₁
  let d₂ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
    e₂ he₂ ψ hAD₂
  exact d₁.disjoint_sides_strictly_nested d₂ hdisjoint
    (isConnected_range he₁.contMDiff.continuous)
    (isConnected_range he₂.contMDiff.continuous) hmeet

end Poincare.Topology.SphereSeparation
