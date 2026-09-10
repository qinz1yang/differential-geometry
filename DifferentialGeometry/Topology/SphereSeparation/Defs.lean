import Mathlib.Topology.Connected.Basic

set_option autoImplicit false

namespace Poincare.Topology.SphereSeparation

open Set

structure SphereSides {X : Type*} [TopologicalSpace X] (S : Set X) where
  compactSide : Set X
  endSide : Set X
  isOpen_compactSide : IsOpen compactSide
  isOpen_endSide : IsOpen endSide
  isConnected_compactSide : IsConnected compactSide
  isConnected_endSide : IsConnected endSide
  disjoint : Disjoint compactSide endSide
  union_eq_compl : compactSide ∪ endSide = Sᶜ
  isCompact_closure_compactSide : IsCompact (closure compactSide)
  not_isCompact_closure_endSide : ¬ IsCompact (closure endSide)
  frontier_compactSide : frontier compactSide = S
  frontier_endSide : frontier endSide = S
  closure_compactSide : closure compactSide = compactSide ∪ S
  closure_endSide : closure endSide = endSide ∪ S
  interior_closure_compactSide : interior (closure compactSide) = compactSide

namespace SphereSides

variable {X : Type*} [TopologicalSpace X] {S C : Set X}

theorem compl_eq_union (d : SphereSides S) :
    Sᶜ = d.compactSide ∪ d.endSide :=
  d.union_eq_compl.symm

theorem compactSide_subset_compl (d : SphereSides S) :
    d.compactSide ⊆ Sᶜ := by
  rw [d.compl_eq_union]
  exact subset_union_left

theorem endSide_subset_compl (d : SphereSides S) :
    d.endSide ⊆ Sᶜ := by
  rw [d.compl_eq_union]
  exact subset_union_right

theorem compactSide_disjoint_sphere (d : SphereSides S) :
    Disjoint d.compactSide S := by
  rw [Set.disjoint_left]
  intro x hxB hxS
  exact d.compactSide_subset_compl hxB hxS

theorem endSide_disjoint_sphere (d : SphereSides S) :
    Disjoint d.endSide S := by
  rw [Set.disjoint_left]
  intro x hxE hxS
  exact d.endSide_subset_compl hxE hxS

theorem compactSide_nonempty (d : SphereSides S) :
    d.compactSide.Nonempty :=
  d.isConnected_compactSide.nonempty

theorem endSide_nonempty (d : SphereSides S) :
    d.endSide.Nonempty :=
  d.isConnected_endSide.nonempty

theorem subset_compactSide_or_subset_endSide (d : SphereSides S)
    (hC : IsPreconnected C) (hCS : C ⊆ Sᶜ) :
    C ⊆ d.compactSide ∨ C ⊆ d.endSide := by
  apply hC.subset_or_subset d.isOpen_compactSide d.isOpen_endSide d.disjoint
  simpa only [d.union_eq_compl] using hCS

theorem subset_compactSide_of_isPreconnected_of_inter_nonempty
    (d : SphereSides S) (hC : IsPreconnected C) (hCS : C ⊆ Sᶜ)
    (hCB : (C ∩ d.compactSide).Nonempty) :
    C ⊆ d.compactSide := by
  exact hC.subset_left_of_subset_union d.isOpen_compactSide d.isOpen_endSide
    d.disjoint (by simpa only [d.union_eq_compl] using hCS) hCB

theorem subset_endSide_of_isPreconnected_of_inter_nonempty
    (d : SphereSides S) (hC : IsPreconnected C) (hCS : C ⊆ Sᶜ)
    (hCE : (C ∩ d.endSide).Nonempty) :
    C ⊆ d.endSide := by
  exact hC.subset_right_of_subset_union d.isOpen_compactSide d.isOpen_endSide
    d.disjoint (by simpa only [d.union_eq_compl] using hCS) hCE

end SphereSides

end Poincare.Topology.SphereSeparation
