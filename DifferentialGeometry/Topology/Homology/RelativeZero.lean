import DifferentialGeometry.Topology.Homology.ConnectedZeroHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian



noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]




theorem integralAbsoluteToRelative_zero_epi (A : Set X) :
    Epi (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g 0) := by
  have := (integralRelativeChainSequence_shortExact A).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    (integralRelativeChainSequence A).g 0 (by intro j; simp)



theorem integralRelativeZero_subsingleton [PathConnectedSpace X]
    (A : Set X) [PathConnectedSpace A] : Subsingleton (integralRelativeHomology 0 A) := by
  have hi := integralSingularHomologyZeroMap_isIso (singularSubspaceInclusion A)
  have hs := (integralRelativeChainSequence_shortExact A).homology_exact₂ 0
  have hz := hs.epi_f_iff.mp (IsIso.epi_of_iso
    (HomologicalComplex.homologyMap (integralSingularChainMap (singularSubspaceInclusion A)) 0))
  exact ModuleCat.subsingleton_of_isZero (@IsZero.of_epi_eq_zero _ _ _ _ _
    (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g 0)
      (integralAbsoluteToRelative_zero_epi A) hz)

end DifferentialGeometry.Topology
