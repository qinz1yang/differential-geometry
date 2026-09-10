import Mathlib.Topology.Connected.Clopen
import DifferentialGeometry.Topology.SphereSeparation.ComplementPair

set_option autoImplicit false

open Set

namespace Poincare.Topology.SphereSeparation

structure LocalTwoSidedAt {X : Type*} [TopologicalSpace X]
    (S : Set X) (x : X) where
  neighborhood : Set X
  negative : Set X
  positive : Set X
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : x ∈ neighborhood
  isConnected_negative : IsConnected negative
  isConnected_positive : IsConnected positive
  disjoint : Disjoint negative positive
  punctured_eq : neighborhood \ S = negative ∪ positive
  central_subset_closure_negative :
    neighborhood ∩ S ⊆ closure negative
  central_subset_closure_positive :
    neighborhood ∩ S ⊆ closure positive


def LocallyTwoSided {X : Type*} [TopologicalSpace X] (S : Set X) : Prop :=
  ∀ x ∈ S, Nonempty (LocalTwoSidedAt S x)

namespace ComplementPair

variable {X : Type*} [TopologicalSpace X] {S : Set X}

private theorem closure_subset_union_separator (p : ComplementPair S) :
    closure p.left ⊆ p.left ∪ S := by
  apply closure_minimal subset_union_left
  have hcompl : (p.left ∪ S)ᶜ = p.right := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxCompl : x ∈ Sᶜ := fun hxS => hx (Or.inr hxS)
      rw [← p.union_eq_compl] at hxCompl
      rcases hxCompl with hxL | hxR
      · exact False.elim (hx (Or.inl hxL))
      · exact hxR
    · intro x hxR hx
      rcases hx with hxL | hxS
      · exact Set.disjoint_left.1 p.disjoint hxL hxR
      · exact p.right_subset_compl hxR hxS
  rw [← isOpen_compl_iff, hcompl]
  exact p.isOpen_right

private theorem closure_right_subset_union_separator (p : ComplementPair S) :
    closure p.right ⊆ p.right ∪ S :=
  p.swap.closure_subset_union_separator

private theorem separator_inter_closure_left_nonempty
    [ConnectedSpace X] (p : ComplementPair S) :
    (S ∩ closure p.left).Nonempty := by
  by_contra hEmpty
  have hClosureSubset : closure p.left ⊆ p.left := by
    intro x hx
    rcases p.closure_subset_union_separator hx with hxL | hxS
    · exact hxL
    · exact False.elim (hEmpty ⟨x, hxS, hx⟩)
  have hClosed : IsClosed p.left :=
    closure_subset_iff_isClosed.1 hClosureSubset
  have hUniv : p.left = Set.univ :=
    IsClopen.eq_univ ⟨hClosed, p.isOpen_left⟩ p.isConnected_left.nonempty
  obtain ⟨x, hxR⟩ := p.isConnected_right.nonempty
  exact Set.disjoint_left.1 p.disjoint (hUniv ▸ Set.mem_univ x) hxR

private theorem separator_inter_closure_right_nonempty
    [ConnectedSpace X] (p : ComplementPair S) :
    (S ∩ closure p.right).Nonempty :=
  p.swap.separator_inter_closure_left_nonempty

private theorem incident_isOpen
    (p : ComplementPair S) (hlocal : LocallyTwoSided S) :
    IsOpen {x : S | (x : X) ∈ closure p.left} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨q⟩ := hlocal x x.2
  have hMeet : (p.left ∩ q.neighborhood).Nonempty := by
    exact (closure_inter_open_nonempty_iff q.isOpen_neighborhood).mp
      ⟨x, hx, q.mem_neighborhood⟩
  obtain ⟨y, hyL, hyU⟩ := hMeet
  have hyPunctured : y ∈ q.neighborhood \ S :=
    ⟨hyU, p.left_subset_compl hyL⟩
  rw [q.punctured_eq] at hyPunctured
  have hHalfSubset :
      q.negative ⊆ p.left ∨ q.positive ⊆ p.left := by
    rcases hyPunctured with hyNeg | hyPos
    · rcases p.subset_left_or_subset_right
          q.isConnected_negative.isPreconnected
          (by
            intro z hz
            have hzPunctured : z ∈ q.neighborhood \ S := by
              rw [q.punctured_eq]
              exact Or.inl hz
            exact hzPunctured.2) with hNeg | hNeg
      · exact Or.inl hNeg
      · exact False.elim (Set.disjoint_left.1 p.disjoint hyL (hNeg hyNeg))
    · rcases p.subset_left_or_subset_right
          q.isConnected_positive.isPreconnected
          (by
            intro z hz
            have hzPunctured : z ∈ q.neighborhood \ S := by
              rw [q.punctured_eq]
              exact Or.inr hz
            exact hzPunctured.2) with hPos | hPos
      · exact Or.inr hPos
      · exact False.elim (Set.disjoint_left.1 p.disjoint hyL (hPos hyPos))
  refine ⟨Subtype.val ⁻¹' q.neighborhood, ?_,
    q.isOpen_neighborhood.preimage continuous_subtype_val, q.mem_neighborhood⟩
  intro z hzU
  have hzCentral : (z : X) ∈ q.neighborhood ∩ S := ⟨hzU, z.2⟩
  rcases hHalfSubset with hNeg | hPos
  · exact closure_mono hNeg (q.central_subset_closure_negative hzCentral)
  · exact closure_mono hPos (q.central_subset_closure_positive hzCentral)

private theorem incident_isClosed (p : ComplementPair S) :
    IsClosed {x : S | (x : X) ∈ closure p.left} :=
  isClosed_closure.preimage continuous_subtype_val

theorem both_components_approach_of_locallyTwoSided
    [ConnectedSpace X] (p : ComplementPair S) (hS : IsConnected S)
    (hlocal : LocallyTwoSided S) :
    S ⊆ closure p.left ∧ S ⊆ closure p.right := by
  let _ : ConnectedSpace S := Subtype.connectedSpace hS
  have hLeftNonempty :
      ({x : S | (x : X) ∈ closure p.left} : Set S).Nonempty := by
    obtain ⟨x, hxS, hxCl⟩ := p.separator_inter_closure_left_nonempty
    exact ⟨⟨x, hxS⟩, hxCl⟩
  have hLeftUniv : {x : S | (x : X) ∈ closure p.left} = Set.univ :=
    IsClopen.eq_univ
      ⟨p.incident_isClosed, p.incident_isOpen hlocal⟩ hLeftNonempty
  have hRightNonempty :
      ({x : S | (x : X) ∈ closure p.right} : Set S).Nonempty := by
    obtain ⟨x, hxS, hxCl⟩ := p.separator_inter_closure_right_nonempty
    exact ⟨⟨x, hxS⟩, hxCl⟩
  have hRightUniv : {x : S | (x : X) ∈ closure p.right} = Set.univ :=
    IsClopen.eq_univ
      ⟨p.swap.incident_isClosed, p.swap.incident_isOpen hlocal⟩ hRightNonempty
  constructor
  · intro x hxS
    have hx : (⟨x, hxS⟩ : S) ∈
        ({y : S | (y : X) ∈ closure p.left} : Set S) := by
      rw [hLeftUniv]
      exact Set.mem_univ _
    exact hx
  · intro x hxS
    have hx : (⟨x, hxS⟩ : S) ∈
        ({y : S | (y : X) ∈ closure p.right} : Set S) := by
      rw [hRightUniv]
      exact Set.mem_univ _
    exact hx

end ComplementPair

end Poincare.Topology.SphereSeparation
