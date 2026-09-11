import DifferentialGeometry.Topology.Homology.SimplexBoundary



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]


def integralSingularAugmentation : (integralSingularChains X).X 0 →ₗ[ℤ] ℤ :=
  (integralSingularChainBasis 0 X).constr (M' := ℤ) ℕ (fun _ => 1)


theorem integralSingularAugmentation_simplex (σ : integralSingularSimplex 0 X) :
    integralSingularAugmentation (integralSimplexChain 0 σ) = 1 := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ


theorem integralSingularAugmentation_boundary :
    integralSingularAugmentation.comp ((integralSingularChains X).d 1 0).hom = 0 := by
  apply (integralSingularChainBasis 1 X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  change integralSingularAugmentation ((integralSingularChains X).d 1 0
    (integralSimplexChain 1 σ)) = 0
  rw [integralSimplexChain_boundary_one, map_sub,
    integralSingularAugmentation_simplex, integralSingularAugmentation_simplex, sub_self]

end DifferentialGeometry.Topology
