import DifferentialGeometry.Topology.SphereSeparation.Nesting
import Mathlib.Order.Preorder.Finite

section

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_innermost_sphereSides
    {X ι : Type*} [TopologicalSpace X] [Finite ι] [Nonempty ι]
    {S : ι → Set X} (d : ∀ i, SphereSides (S i))
    (hS : ∀ i, IsConnected (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j)) :
    ∃ i : ι, ∀ j : ι, j ≠ i → Disjoint (closure (d i).compactSide) (S j) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i, hmin⟩ := (Finset.univ : Finset ι).exists_minimalFor
    (fun j => closure (d j).compactSide) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  intro j hji
  have hSiSj : Disjoint (S i) (S j) := hdisjoint hji.symm
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hxiSide : x ∈ (d i).compactSide := by
    rw [(d i).closure_compactSide] at hxi
    exact hxi.resolve_right (fun h => Set.disjoint_left.mp hSiSj h hxj)
  have hxjClosure : x ∈ closure (d j).compactSide := by
    rw [(d j).closure_compactSide]
    exact Or.inr hxj
  obtain ⟨y, hyi, hyj⟩ := mem_closure_iff.mp hxjClosure
    (d i).compactSide (d i).isOpen_compactSide hxiSide
  have hmeet : ((d i).compactSide ∩ (d j).compactSide).Nonempty := ⟨y, hyi, hyj⟩
  rcases ((d i).disjoint_sides_strictly_nested (d j) hSiSj (hS i) (hS j) hmeet).or with
    hij | hji'
  · exact (d j).compactSide_disjoint_sphere.le_bot ⟨hij.1.le hxi, hxj⟩
  · exact hji'.2.2.not_ge (hmin.2 (Finset.mem_univ j) hji'.2.2.le)

theorem exists_sphereSides_compactSide_disjoint_iUnion
    {X ι : Type*} [TopologicalSpace X] [Finite ι] [Nonempty ι]
    {S : ι → Set X} (d : ∀ i, SphereSides (S i))
    (hS : ∀ i, IsConnected (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j)) :
    ∃ i : ι, Disjoint (d i).compactSide (⋃ j, S j) ∧
      ∀ j : ι, j ≠ i → Disjoint (closure (d i).compactSide) (S j) := by
  obtain ⟨i, hi⟩ := exists_innermost_sphereSides d hS hdisjoint
  refine ⟨i, ?_, hi⟩
  rw [Set.disjoint_left]
  intro x hxi hx
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
  by_cases hji : j = i
  · subst j
    exact (d i).compactSide_disjoint_sphere.le_bot ⟨hxi, hxj⟩
  · exact Set.disjoint_left.mp (hi j hji) (subset_closure hxi) hxj

end DifferentialGeometry.Topology.SphereSeparation

end
