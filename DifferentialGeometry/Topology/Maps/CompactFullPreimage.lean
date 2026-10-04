import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.Proper.Basic
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

/-! Properness of literal full-preimage maps from the original compact carrier. -/

set_option autoImplicit false
noncomputable section
open Set Topology
namespace DifferentialGeometry.Topology

theorem isProperMap_restrictPreimage_of_compact {M H : Type*}
    [TopologicalSpace M] [CompactSpace M] [TopologicalSpace H] [T2Space H]
    (f : M → H) (hf : Continuous f) (A : Set H) :
    IsProperMap (A.restrictPreimage f) := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨hf.restrictPreimage, hf.isClosedMap.restrictPreimage A, ?_⟩
  intro y
  rw [Subtype.isCompact_iff]
  have heq : Subtype.val '' ((A.restrictPreimage f) ⁻¹' {y}) = f ⁻¹' {y.val} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg Subtype.val hz
    · intro hx
      change f x = y.val at hx
      refine ⟨⟨x, ?_⟩, ?_, rfl⟩
      · change f x ∈ A
        rw [hx]
        exact y.property
      · exact Subtype.ext hx
  rw [heq]
  exact (isClosed_singleton.preimage hf).isCompact

def compactFullPreimageMap {M H : Type*} [TopologicalSpace H]
    (f : M → H) (W : Set H) (B : Set W) :
    (f ⁻¹' ((Subtype.val : W → H) '' B)) → B :=
  (IsEmbedding.subtypeVal.homeomorphImage B).symm ∘
    (((Subtype.val : W → H) '' B).restrictPreimage f)

theorem compactFullPreimageMap_val {M H : Type*}
    [TopologicalSpace H]
    (f : M → H) (W : Set H) (B : Set W)
    (x : f ⁻¹' ((Subtype.val : W → H) '' B)) :
    ((compactFullPreimageMap f W B x : W) : H) = f x := by
  have heq := (IsEmbedding.subtypeVal.homeomorphImage B).apply_symm_apply
    ((((Subtype.val : W → H) '' B).restrictPreimage f) x)
  exact congrArg Subtype.val heq

theorem compactFullPreimage_source {M H : Type*}
    (f : M → H) (W : Set H) (B : Set W) :
    range (Subtype.val : (f ⁻¹' ((Subtype.val : W → H) '' B)) → M) =
      f ⁻¹' ((Subtype.val : W → H) '' B) := Subtype.range_coe

theorem isProperMap_compactFullPreimageMap {M H : Type*}
    [TopologicalSpace M] [CompactSpace M] [TopologicalSpace H] [T2Space H]
    (f : M → H) (hf : Continuous f) (W : Set H) (B : Set W) :
    IsProperMap (compactFullPreimageMap f W B) :=
  (IsEmbedding.subtypeVal.homeomorphImage B).symm.isProperMap.comp
    (isProperMap_restrictPreimage_of_compact f hf ((Subtype.val : W → H) '' B))

theorem ClosedOrientedManifold.isProperMap_fullPreimage {n : ℕ}
    (M : ClosedOrientedManifold n) {H : Type*} [TopologicalSpace H] [T2Space H]
    (f : M.Carrier → H) (hf : Continuous f) (W : Set H) (B : Set W) :
    IsProperMap (compactFullPreimageMap f W B) :=
  isProperMap_compactFullPreimageMap f hf W B

def threeSphereHeight (x : standardThreeSphere.Carrier) : ℝ := x.val 0

def threeSphereHeightBase : Set (univ : Set ℝ) := {w | -1 < w.val ∧ w.val < 1}

def threeSphereHeightFullPreimage :=
  threeSphereHeight ⁻¹' ((Subtype.val : ↥(univ : Set ℝ) → ℝ) '' threeSphereHeightBase)

def threeSphereRestrictedHeight : threeSphereHeightFullPreimage → threeSphereHeightBase :=
  compactFullPreimageMap threeSphereHeight univ threeSphereHeightBase

theorem threeSphereRestrictedHeight_isProperMap : IsProperMap threeSphereRestrictedHeight := by
  apply standardThreeSphere.toClosedOrientedManifold.isProperMap_fullPreimage
  unfold threeSphereHeight
  fun_prop

theorem threeSphereRestrictedHeight_val (x : threeSphereHeightFullPreimage) :
    ((threeSphereRestrictedHeight x : (univ : Set ℝ)) : ℝ) = x.val.val 0 :=
  compactFullPreimageMap_val threeSphereHeight univ threeSphereHeightBase x

theorem threeSphereHeightFullPreimage_eq :
    threeSphereHeightFullPreimage = {x | -1 < x.val 0 ∧ x.val 0 < 1} := by
  ext x
  constructor
  · rintro ⟨w, hw, heq⟩
    change -1 < threeSphereHeight x ∧ threeSphereHeight x < 1
    rw [← heq]
    exact hw
  · intro hx
    exact ⟨⟨threeSphereHeight x, mem_univ _⟩, hx, rfl⟩

end DifferentialGeometry.Topology
