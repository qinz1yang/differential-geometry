import DifferentialGeometry.Topology.Homology.TwoSetSmallChains
import DifferentialGeometry.Topology.Homology.ChainCokernelElements



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]



def integralExcisionSmallMap (A B : Set X) :
    integralRelativeChains (subspaceIntersection A B) ⟶ integralSmallRelativeChains (twoSetCover A B) false :=
  cokernel.map _ _
    (integralSingularChainMap (singularPairRestriction (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)))
    (integralSingularChainToSmall (twoSetCover A B) true)
    (integralSingularTwoSetSmall_square A B)




instance integralExcisionSmallMap_isIso (A B : Set X) :
    IsIso (integralExcisionSmallMap A B) := by
  unfold integralExcisionSmallMap
  apply isIso_chainCokernelMap_of_representatives _ _
    (integralSingularChainMap (singularPairRestriction (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B))) _ (integralSingularTwoSetSmall_square A B)
  · intro n c b hb
    have he := congrArg Subtype.val hb
    change (integralSingularChainMap (singularSubspaceInclusion A)).f n b =
      (integralSingularChainMap (singularSubspaceInclusion B)).f n c at he
    have hcA : (integralSingularChainMap (singularSubspaceInclusion B)).f n c ∈
        integralSingularChainsIn n A := by
      rw [← he, integralSingularChainsIn_eq_range]
      exact ⟨b, rfl⟩
    have hc := (integralSingularChainsIn_subspace_iff n A B c).mpr hcA
    rw [integralSingularChainsIn_eq_range] at hc
    exact hc
  · intro n d
    obtain ⟨a, b, hab⟩ := integralSingularTwoSetSmallChains_decompose n A B d
    refine ⟨b, a, ?_⟩
    apply Subtype.ext
    change (integralSingularChainMap (singularSubspaceInclusion A)).f n a =
      d.val - (integralSingularChainMap (singularSubspaceInclusion B)).f n b
    rw [← hab]
    abel

set_option backward.isDefEq.respectTransparency false in


theorem integralExcisionSmallMap_comparison (A B : Set X) :
    integralExcisionSmallMap A B ≫ integralSmallRelativeComparison (twoSetCover A B) false =
      integralRelativeChainMap (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B) := by
  apply (cancel_epi (cokernel.π (integralSingularChainMap
    (singularSubspaceInclusion (subspaceIntersection A B))))).mp
  simp only [Category.assoc, integralExcisionSmallMap, integralSmallRelativeComparison,
    integralRelativeChainMap, cokernel.π_desc_assoc, cokernel.π_desc]
  rw [← Category.assoc, integralSingularChainToSmall_inclusion]
  rfl

end DifferentialGeometry.Topology
