import DifferentialGeometry.Topology.Homology.ContractiblePair
import DifferentialGeometry.Topology.Homology.ConnectedZeroHomology



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]



theorem integralAbsoluteToRelative_one_isIso_of_contractible [PathConnectedSpace X]
    (A : Set X) [ContractibleSpace A] :
    IsIso (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g 1) := by
  let := integralSingularHomology_subsingleton_of_contractible 1 (by omega) A
  have hz := ModuleCat.isZero_of_subsingleton (integralSingularHomology 1 A)
  have hm := ((integralRelativeChainSequence_shortExact A).homology_exact₂ 1).mono_g (hz.eq_of_src _ _)
  have hi := integralSingularHomologyZeroMap_isIso (singularSubspaceInclusion A)
  have hs := (integralRelativeChainSequence_shortExact A).homology_exact₁ 1 0 (by simp)
  have hδ := hs.mono_g_iff.mp (IsIso.mono_of_iso
    (HomologicalComplex.homologyMap (integralSingularChainMap (singularSubspaceInclusion A)) 0))
  have he := ((integralRelativeChainSequence_shortExact A).homology_exact₃ 1 0 (by simp)).epi_f hδ
  exact isIso_of_mono_of_epi _


def integralAbsoluteToRelativeOneIsoOfContractible [PathConnectedSpace X]
    (A : Set X) [ContractibleSpace A] :
    integralSingularHomology 1 X ≅ integralRelativeHomology 1 A :=
  @asIso _ _ _ _ (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g 1)
    (integralAbsoluteToRelative_one_isIso_of_contractible A)



theorem integralRelativeConnecting_zero_injective [ContractibleSpace X] (A : Set X) :
    Function.Injective (integralRelativeConnecting 0 A) := by
  let := integralSingularHomology_subsingleton_of_contractible 1 (by omega) X
  have hz := ModuleCat.isZero_of_subsingleton (integralSingularHomology 1 X)
  have hm := ((integralRelativeChainSequence_shortExact A).homology_exact₃ 1 0 (by simp)).mono_g
    (hz.eq_of_src _ _)
  exact (ModuleCat.mono_iff_injective _).mp hm

end DifferentialGeometry.Topology
