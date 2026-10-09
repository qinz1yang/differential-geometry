import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite

/-!
Two actual connected open sides identify all native connected components of their complement.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology

universe u

namespace GC.GraphManifold

variable {X : Type u} [TopologicalSpace X]
variable (A : Bool → Set X) (Z : Set X)
variable (hA : ∀ t, IsConnected (A t)) (hd : Disjoint (A false) (A true))
variable (ho : ∀ t, IsOpen (A t)) (hz : Zᶜ = A false ∪ A true)

private def twoOpenSidesSubtype (t : Bool) : Set ↥(Zᶜ) := Subtype.val ⁻¹' A t

include hz in
omit [TopologicalSpace X] in
private theorem twoOpenSides_subset (t : Bool) : A t ⊆ Zᶜ := by
  rw [hz]
  cases t
  · exact subset_union_left
  · exact subset_union_right

include hz in
omit [TopologicalSpace X] in
private theorem twoOpenSidesSubtype_image (t : Bool) :
    Subtype.val '' twoOpenSidesSubtype A Z t = A t := by
  rw [twoOpenSidesSubtype, Subtype.image_preimage_coe,
    inter_eq_right.mpr (twoOpenSides_subset A Z hz t)]

include hA hz in
private theorem twoOpenSidesSubtype_connected (t : Bool) :
    IsConnected (twoOpenSidesSubtype A Z t) := by
  obtain ⟨x, hx⟩ := (hA t).nonempty
  refine ⟨⟨⟨x, twoOpenSides_subset A Z hz t hx⟩, hx⟩, ?_⟩
  apply IsInducing.subtypeVal.isPreconnected_image.mp
  rw [twoOpenSidesSubtype_image A Z hz t]
  exact (hA t).isPreconnected

include hd hz in
omit [TopologicalSpace X] in
private theorem twoOpenSidesSubtype_compl (t : Bool) :
    (twoOpenSidesSubtype A Z t)ᶜ = twoOpenSidesSubtype A Z (!t) := by
  ext x
  have hx : x.val ∈ A false ∪ A true := hz ▸ x.property
  cases t
  · change (x.val ∉ A false) ↔ x.val ∈ A true
    constructor
    · intro hnot
      exact hx.resolve_left hnot
    · intro ht hf
      exact hd.le_bot ⟨hf, ht⟩
  · change (x.val ∉ A true) ↔ x.val ∈ A false
    constructor
    · intro hnot
      exact hx.resolve_right hnot
    · intro hf ht
      exact hd.le_bot ⟨hf, ht⟩

include hd ho hz in
private theorem twoOpenSidesSubtype_clopen (t : Bool) :
    IsClopen (twoOpenSidesSubtype A Z t) := by
  have hopen (s : Bool) : IsOpen (twoOpenSidesSubtype A Z s) :=
    (ho s).preimage continuous_subtype_val
  refine ⟨?_, hopen t⟩
  apply isOpen_compl_iff.mp
  rw [twoOpenSidesSubtype_compl A Z hd hz t]
  exact hopen (!t)

include hd in
omit [TopologicalSpace X] in
private theorem twoOpenSidesSubtype_disjoint :
    Pairwise (fun i j => Disjoint (twoOpenSidesSubtype A Z i) (twoOpenSidesSubtype A Z j)) := by
  intro i j hij
  cases i <;> cases j
  · exact (hij rfl).elim
  · exact hd.preimage Subtype.val
  · exact hd.symm.preimage Subtype.val
  · exact (hij rfl).elim

include hz in
omit [TopologicalSpace X] in
private theorem twoOpenSidesSubtype_cover : ⋃ t, twoOpenSidesSubtype A Z t = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  rcases (show x.val ∈ A false ∪ A true from hz ▸ x.property) with hf | ht
  · exact ⟨false, hf⟩
  · exact ⟨true, ht⟩


def twoOpenSidesComponentsEquiv : ConnectedComponents ↥(Zᶜ) ≃ Bool :=
  ConnectedComponents.equivOfIsClopenOfIsConnected
    (twoOpenSidesSubtype_clopen A Z hd ho hz) (twoOpenSidesSubtype_disjoint A Z hd)
    (twoOpenSidesSubtype_cover A Z hz) (twoOpenSidesSubtype_connected A Z hA hz)

theorem twoOpenSidesComponentsEquiv_mk (t : Bool) (x : ↥(Zᶜ)) (hx : x.val ∈ A t) :
    twoOpenSidesComponentsEquiv A Z hA hd ho hz (ConnectedComponents.mk x) = t :=
  ConnectedComponents.equivOfIsClopenOfIsConnected_mk
    (twoOpenSidesSubtype_clopen A Z hd ho hz) (twoOpenSidesSubtype_disjoint A Z hd)
    (twoOpenSidesSubtype_cover A Z hz) (twoOpenSidesSubtype_connected A Z hA hz) x hx

theorem twoOpenSidesComponentsEquiv_mk_eq_iff (x : ↥(Zᶜ)) (t : Bool) :
    twoOpenSidesComponentsEquiv A Z hA hd ho hz (ConnectedComponents.mk x) = t ↔ x.val ∈ A t := by
  constructor
  · intro he
    rcases (show x.val ∈ A false ∪ A true from hz ▸ x.property) with hf | ht
    · have hlabel := twoOpenSidesComponentsEquiv_mk A Z hA hd ho hz false x hf
      exact he.symm.trans hlabel ▸ hf
    · have hlabel := twoOpenSidesComponentsEquiv_mk A Z hA hd ho hz true x ht
      exact he.symm.trans hlabel ▸ ht
  · exact twoOpenSidesComponentsEquiv_mk A Z hA hd ho hz t x

include hA hd ho hz in
theorem twoOpenSides_connectedComponent (t : Bool) (x : ↥(Zᶜ)) (hx : x.val ∈ A t) :
    connectedComponent x = Subtype.val ⁻¹' A t :=
  subset_antisymm ((twoOpenSidesSubtype_clopen A Z hd ho hz t).connectedComponent_subset hx)
    ((twoOpenSidesSubtype_connected A Z hA hz t).subset_connectedComponent hx)

include hA hd ho hz in
theorem twoOpenSides_connectedComponentIn (t : Bool) (x : X) (hx : x ∈ A t) :
    connectedComponentIn Zᶜ x = A t := by
  have hxc := twoOpenSides_subset A Z hz t hx
  rw [connectedComponentIn_eq_image hxc,
    twoOpenSides_connectedComponent A Z hA hd ho hz t ⟨x, hxc⟩ hx,
    Subtype.image_preimage_coe, inter_eq_right.mpr (twoOpenSides_subset A Z hz t)]

open Classical in
theorem twoOpenSides_connectedComponentIn_eq (x : X) :
    connectedComponentIn Zᶜ x =
      if hx : x ∈ Zᶜ then A (twoOpenSidesComponentsEquiv A Z hA hd ho hz
        (ConnectedComponents.mk ⟨x, hx⟩)) else ∅ := by
  by_cases hx : x ∈ Zᶜ
  · rw [dite_eq_left hx]
    let y : ↥(Zᶜ) := ⟨x, hx⟩
    let t := twoOpenSidesComponentsEquiv A Z hA hd ho hz (ConnectedComponents.mk y)
    have ht : y.val ∈ A t := (twoOpenSidesComponentsEquiv_mk_eq_iff A Z hA hd ho hz y t).mp rfl
    exact twoOpenSides_connectedComponentIn A Z hA hd ho hz t x ht
  · rw [dite_eq_right hx]
    exact connectedComponentIn_eq_empty hx

include hA hd ho hz in
theorem twoOpenSides_components_finite : Finite (ConnectedComponents ↥(Zᶜ)) :=
  Finite.of_equiv Bool (twoOpenSidesComponentsEquiv A Z hA hd ho hz).symm

include hA hd ho hz in
theorem twoOpenSides_components_card : Nat.card (ConnectedComponents ↥(Zᶜ)) = 2 := by
  rw [Nat.card_congr (twoOpenSidesComponentsEquiv A Z hA hd ho hz)]
  simp

end GC.GraphManifold
