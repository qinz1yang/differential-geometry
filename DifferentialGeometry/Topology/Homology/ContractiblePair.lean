import DifferentialGeometry.Topology.Homology.OpenExcision



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]



theorem integralAbsoluteToRelative_isIso_of_contractible (n : ℕ) (A : Set X) [ContractibleSpace A] :
    IsIso (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g (n + 2)) := by
  let := integralSingularHomology_subsingleton_of_contractible (n + 2) (by omega) A
  let := integralSingularHomology_subsingleton_of_contractible (n + 1) (by omega) A
  have hz₂ := ModuleCat.isZero_of_subsingleton (integralSingularHomology (n + 2) A)
  have hz₁ := ModuleCat.isZero_of_subsingleton (integralSingularHomology (n + 1) A)
  have hm := ((integralRelativeChainSequence_shortExact A).homology_exact₂ (n + 2)).mono_g
    (hz₂.eq_of_src _ _)
  have he := ((integralRelativeChainSequence_shortExact A).homology_exact₃ (n + 2) (n + 1) (by simp)).epi_f
    (hz₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _


def integralAbsoluteToRelativeIsoOfContractible (n : ℕ) (A : Set X) [ContractibleSpace A] :
    integralSingularHomology (n + 2) X ≅ integralRelativeHomology (n + 2) A := by
  exact @asIso _ _ _ _ (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g (n + 2))
    (integralAbsoluteToRelative_isIso_of_contractible n A)




def integralHomologyContractibleCoverEquiv (n : ℕ) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ) :
    integralSingularHomology (n + 2) X ≃ₗ[ℤ] integralSingularHomology (n + 1) (subspaceIntersection A B) :=
  ((integralAbsoluteToRelativeIsoOfContractible n A).toLinearEquiv.trans
    (integralRelativeOpenExcisionIso (n + 2) A B hA hB hcover).symm.toLinearEquiv).trans
      (integralRelativeConnectingEquivOfContractible (n + 1) (by omega) (subspaceIntersection A B))

end DifferentialGeometry.Topology
