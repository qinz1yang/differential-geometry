import Poincare.Topology.Homology.ConnectedZeroHomology
import Poincare.Topology.Homology.RelativeMaps
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Actual relative H0 for a path-connected pair -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The actual absolute-to-relative map is surjective in degree zero,
since the original chain quotient is degreewise surjective and has no
outgoing differential in degree zero. -/
theorem integralAbsoluteToRelative_zero_epi (A : Set X) :
    Epi (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g 0) := by
  have := (integralRelativeChainSequence_shortExact A).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    (integralRelativeChainSequence A).g 0 (by intro j; simp)

theorem integralRelativeHomologyMap_zero_eq_of_joined
    {Y : Type u} [TopologicalSpace Y]
    (f g : C(X, Y)) (A : Set X) (B : Set Y)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (h : ∀ x, Joined (f x) (g x)) :
    integralRelativeHomologyMap 0 f hf = integralRelativeHomologyMap 0 g hg := by
  have hsurj : Function.Surjective (integralAbsoluteToRelative 0 A) :=
    (ModuleCat.epi_iff_surjective _).mp (integralAbsoluteToRelative_zero_epi A)
  have habs := integralSingularHomologyMap_zero_eq_of_joined f g h
  have hcomp : (integralRelativeHomologyMap 0 f hf).comp (integralAbsoluteToRelative 0 A) =
      (integralRelativeHomologyMap 0 g hg).comp (integralAbsoluteToRelative 0 A) := by
    rw [← integralAbsoluteToRelative_natural, ← integralAbsoluteToRelative_natural, habs]
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := hsurj a
  exact LinearMap.congr_fun hcomp b

/-- For a path-connected original pair, actual relative H0 vanishes by
the actual exact sequence and the proved H0 inclusion isomorphism. -/
theorem integralRelativeZero_subsingleton [PathConnectedSpace X]
    (A : Set X) [PathConnectedSpace A] : Subsingleton (integralRelativeHomology 0 A) := by
  have hi := integralSingularHomologyZeroMap_isIso (singularSubspaceInclusion A)
  have hs := (integralRelativeChainSequence_shortExact A).homology_exact₂ 0
  have hz := hs.epi_f_iff.mp (IsIso.epi_of_iso
    (HomologicalComplex.homologyMap (integralSingularChainMap (singularSubspaceInclusion A)) 0))
  exact ModuleCat.subsingleton_of_isZero (@IsZero.of_epi_eq_zero _ _ _ _ _
    (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g 0)
      (integralAbsoluteToRelative_zero_epi A) hz)

end Poincare.Topology

section

open Set

namespace Poincare.Topology

theorem integralAbsoluteToRelative_zero_vertex_of_mem
    {X : Type u} [TopologicalSpace X] (A : Set X) (x : X) (hx : x ∈ A) :
    integralAbsoluteToRelative 0 A (integralZeroChainClass (integralVertexChain x)) = 0 := by
  have h := (integralRelative_exact_absolute 0 A).apply_apply_eq_zero
    (integralZeroChainClass (integralVertexChain (⟨x, hx⟩ : A)))
  rw [integralZeroChainClass_map, integralVertexChain_map] at h
  exact h

theorem integralRelativeHomologyMap_zero_vertex
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) (x : X) :
    integralRelativeHomologyMap 0 f hf
      (integralAbsoluteToRelative 0 A (integralZeroChainClass (integralVertexChain x))) =
    integralAbsoluteToRelative 0 B (integralZeroChainClass (integralVertexChain (f x))) := by
  have h := LinearMap.congr_fun (integralAbsoluteToRelative_natural 0 f hf)
    (integralZeroChainClass (integralVertexChain x))
  change integralAbsoluteToRelative 0 B
      (integralSingularHomologyMap 0 f (integralZeroChainClass (integralVertexChain x))) =
    integralRelativeHomologyMap 0 f hf
      (integralAbsoluteToRelative 0 A (integralZeroChainClass (integralVertexChain x))) at h
  rw [integralZeroChainClass_map, integralVertexChain_map] at h
  exact h.symm

end Poincare.Topology

end
