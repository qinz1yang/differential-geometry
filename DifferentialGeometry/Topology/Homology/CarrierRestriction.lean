import DifferentialGeometry.Topology.Homology.ChainsIn
import DifferentialGeometry.Topology.Homology.SubdivisionNaturality



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]


instance integralSingularChainsIn_module (n : ℕ) (A : Set X) :
    Module ℤ (integralSingularChainsIn n A) := (integralSingularChainsIn n A).module


theorem integralSingularChainInclusion_injective (n : ℕ) (A : Set X) :
    Function.Injective ((integralSingularChainMap (singularSubspaceInclusion A)).f n) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance



def integralSingularChainCarrierEquiv (n : ℕ) (A : Set X) :
    (integralSingularChains A).X n ≃ₗ[ℤ] integralSingularChainsIn n A :=
  (LinearEquiv.ofInjective ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom
    (integralSingularChainInclusion_injective n A)).trans
      (LinearEquiv.ofEq _ _ (integralSingularChainsIn_eq_range n A).symm)


theorem integralSingularChainCarrierEquiv_coe (n : ℕ) (A : Set X)
    (c : (integralSingularChains A).X n) :
    (integralSingularChainCarrierEquiv n A c).val =
      (integralSingularChainMap (singularSubspaceInclusion A)).f n c := rfl


def integralSingularChainRestriction (n : ℕ) (A : Set X) :
    integralSingularChainsIn n A →ₗ[ℤ] (integralSingularChains A).X n :=
  (integralSingularChainCarrierEquiv n A).symm.toLinearMap


theorem integralSingularChainRestriction_inclusion (n : ℕ) (A : Set X)
    (c : integralSingularChainsIn n A) :
    (integralSingularChainMap (singularSubspaceInclusion A)).f n
      (integralSingularChainRestriction n A c) = c.val :=
  congrArg Subtype.val ((integralSingularChainCarrierEquiv n A).apply_symm_apply c)



theorem integralSingularChainRestriction_boundary (n : ℕ) (A : Set X)
    (c : integralSingularChainsIn (n + 1) A) :
    integralSingularChainRestriction n A
      ⟨(integralSingularChains X).d (n + 1) n c.val, integralSingularChainsIn_boundary n A c.property⟩ =
      (integralSingularChains A).d (n + 1) n (integralSingularChainRestriction (n + 1) A c) := by
  apply integralSingularChainInclusion_injective n A
  rw [integralSingularChainRestriction_inclusion, integralSingularChainMap_boundary,
    integralSingularChainRestriction_inclusion]

end DifferentialGeometry.Topology
