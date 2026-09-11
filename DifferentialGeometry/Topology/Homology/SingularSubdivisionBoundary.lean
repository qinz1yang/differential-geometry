import DifferentialGeometry.Topology.Homology.UniversalSubdivisionFaces



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]



theorem integralSingularSubdivision_boundary_simplex (n : ℕ)
    (σ : integralSingularSimplex (n + 1) X) :
    (integralSingularChains X).d (n + 1) n
      (integralSingularSubdivision (n + 1) (integralSimplexChain (n + 1) σ)) =
        integralSingularSubdivision n ((integralSingularChains X).d (n + 1) n
          (integralSimplexChain (n + 1) σ)) := by
  rw [integralSingularSubdivision_simplex, ← singularSimplexChainPush_boundary,
    universalSimplexSubdivision_boundary, map_sum, integralSimplexChain_boundary, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, map_zsmul, singularSimplexChainPush_face, integralSingularSubdivision_simplex]



theorem integralSingularSubdivision_boundary (n : ℕ) :
    ((integralSingularChains X).d (n + 1) n).hom.comp (integralSingularSubdivision (n + 1)) =
      (integralSingularSubdivision n).comp ((integralSingularChains X).d (n + 1) n).hom := by
  apply (integralSingularChainBasis (n + 1) X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  exact integralSingularSubdivision_boundary_simplex n σ



def integralSingularSubdivisionChainMap : integralSingularChains X ⟶ integralSingularChains X where
  f n := ModuleCat.ofHom (integralSingularSubdivision n)
  comm' i j h := by
    change j + 1 = i at h
    subst i
    apply ModuleCat.hom_ext
    exact integralSingularSubdivision_boundary j

end DifferentialGeometry.Topology
