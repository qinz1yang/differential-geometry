import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.SetTheory.Cardinal.Finite

section
set_option autoImplicit false

open Set

namespace DifferentialGeometry.Topology

private theorem eq_or_eq_of_card_le_two {X : Type*} (hcard : ENat.card X ≤ 2)
    {a b : X} (hab : a ≠ b) (x : X) : x = a ∨ x = b := by
  classical
  by_contra h
  have hxa : x ≠ a := fun hxa => h (Or.inl hxa)
  have hxb : x ≠ b := fun hxb => h (Or.inr hxb)
  let f : Fin 3 → X := ![a, b, x]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hh := (ENat.card_le_card_of_injective hinj).trans hcard
  norm_num at hh

theorem isConnected_open_partition_of_card_connectedComponents_le_two
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hdis : Disjoint A B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hcard : ENat.card (ConnectedComponents ↥(A ∪ B)) ≤ 2) :
    IsConnected A ∧ IsConnected B := by
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  let a' : ↥(A ∪ B) := ⟨a, Or.inl ha⟩
  let b' : ↥(A ∪ B) := ⟨b, Or.inr hb⟩
  have himg (z : ↥(A ∪ B)) :
      IsConnected ((Subtype.val : ↥(A ∪ B) → X) '' connectedComponent z) :=
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have hsub (z : ↥(A ∪ B)) :
      (Subtype.val : ↥(A ∪ B) → X) '' connectedComponent z ⊆ A ∪ B := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hsideA : (Subtype.val : ↥(A ∪ B) → X) '' connectedComponent a' ⊆ A :=
    (himg a').isPreconnected.subset_left_of_subset_union hA hB hdis (hsub a')
      ⟨a, ⟨a', mem_connectedComponent, rfl⟩, ha⟩
  have hsideB : (Subtype.val : ↥(A ∪ B) → X) '' connectedComponent b' ⊆ B :=
    (himg b').isPreconnected.subset_right_of_subset_union hA hB hdis (hsub b')
      ⟨b, ⟨b', mem_connectedComponent, rfl⟩, hb⟩
  have hab : ConnectedComponents.mk a' ≠ ConnectedComponents.mk b' := by
    intro h
    have heq := ConnectedComponents.coe_eq_coe.mp h
    have hba : b' ∈ connectedComponent a' := by rw [heq]; exact mem_connectedComponent
    exact hdis.le_bot ⟨hsideA ⟨b', hba, rfl⟩, hb⟩
  have hAeq : A = (Subtype.val : ↥(A ∪ B) → X) '' connectedComponent a' := by
    apply subset_antisymm ?_ hsideA
    intro x hx
    let x' : ↥(A ∪ B) := ⟨x, Or.inl hx⟩
    rcases eq_or_eq_of_card_le_two hcard hab (ConnectedComponents.mk x') with h | h
    · have heq := ConnectedComponents.coe_eq_coe.mp h
      exact ⟨x', by rw [← heq]; exact mem_connectedComponent, rfl⟩
    · have heq := ConnectedComponents.coe_eq_coe.mp h
      have hxb : x' ∈ connectedComponent b' := by rw [← heq]; exact mem_connectedComponent
      exact (hdis.le_bot ⟨hx, hsideB ⟨x', hxb, rfl⟩⟩).elim
  have hBeq : B = (Subtype.val : ↥(A ∪ B) → X) '' connectedComponent b' := by
    apply subset_antisymm ?_ hsideB
    intro x hx
    let x' : ↥(A ∪ B) := ⟨x, Or.inr hx⟩
    rcases eq_or_eq_of_card_le_two hcard hab (ConnectedComponents.mk x') with h | h
    · have heq := ConnectedComponents.coe_eq_coe.mp h
      have hxa : x' ∈ connectedComponent a' := by rw [← heq]; exact mem_connectedComponent
      exact (hdis.le_bot ⟨hsideA ⟨x', hxa, rfl⟩, hx⟩).elim
    · have heq := ConnectedComponents.coe_eq_coe.mp h
      exact ⟨x', by rw [← heq]; exact mem_connectedComponent, rfl⟩
  exact ⟨hAeq.symm ▸ himg a', hBeq.symm ▸ himg b'⟩

end DifferentialGeometry.Topology

end
