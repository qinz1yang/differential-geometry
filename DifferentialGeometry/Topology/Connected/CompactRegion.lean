import DifferentialGeometry.Topology.Connected.FrontierCover
import Mathlib.Topology.Compactness.Compact

open Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [NoncompactSpace X]

theorem subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hconn : IsPreconnected Bᶜ) (hfront : frontier A ⊆ B) : A ⊆ B := by
  intro x hxA
  by_contra hxB
  have hxint : x ∈ interior A := (mem_interior_iff_notMem_frontier hxA).mpr
    (fun hx => hxB (hfront hx))
  have hsub : Bᶜ ⊆ interior A :=
    subset_interior_of_isPreconnected_of_disjoint_frontier hconn
      (disjoint_compl_left.mono_right hfront) ⟨x, hxB, hxint⟩
  apply (hA.union hB).ne_univ
  apply eq_univ_of_forall
  intro y
  by_cases hy : y ∈ B
  · exact Or.inr hy
  · exact Or.inl (interior_subset (hsub hy))

variable [T2Space X]

theorem eq_of_isCompact_of_frontier_eq
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hAreg : closure (interior A) = A) (hBreg : closure (interior B) = B)
    (hBint : IsPreconnected (interior B)) (hBext : IsPreconnected Bᶜ)
    (hne : A.Nonempty) (hfront : frontier A = frontier B) : A = B := by
  have hAB : A ⊆ B := subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl
    hA hB hBext (hfront.subset.trans hB.isClosed.frontier_subset)
  have hAint : (interior A).Nonempty := by
    by_contra h
    have hempty := not_nonempty_iff_eq_empty.mp h
    rw [hempty, closure_empty] at hAreg
    exact hne.ne_empty hAreg.symm
  obtain ⟨x, hx⟩ := hAint
  exact Subset.antisymm hAB
    (subset_of_frontier_subset_of_closure_interior_eq hA.isClosed hBreg hBint
      hfront.subset ⟨x, interior_mono hAB hx, hx⟩)

end DifferentialGeometry.Topology
