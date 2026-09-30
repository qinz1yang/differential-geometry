import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Indexed

namespace DifferentialGeometry.Topology

open Set

theorem exists_pair_cover_of_finite_cover {X ι : Type*} [Finite ι]
    (P : Set X → Prop) (hne : ∃ U, P U)
    (hmerge : ∀ U V W, P U → P V → P W →
      ∃ A B, P A ∧ P B ∧ U ∪ V ∪ W ⊆ A ∪ B)
    (U : ι → Set X) (hU : ∀ i, P (U i)) (hcover : (⋃ i, U i) = univ) :
    ∃ A B, P A ∧ P B ∧ A ∪ B = univ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hfinite (s : Finset ι) :
      ∃ A B, P A ∧ P B ∧ (⋃ i ∈ s, U i) ⊆ A ∪ B := by
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨A, hA⟩ := hne
        exact ⟨A, A, hA, hA, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨A, B, hA, hB, hs⟩ := ih
        obtain ⟨C, D, hC, hD, hCD⟩ := hmerge (U i) A B (hU i) hA hB
        refine ⟨C, D, hC, hD, ?_⟩
        intro x hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hCD (Or.inl (Or.inl hxj))
        · rcases hs (mem_iUnion₂.mpr ⟨j, hj, hxj⟩) with hxA | hxB
          · exact hCD (Or.inl (Or.inr hxA))
          · exact hCD (Or.inr hxB)
  obtain ⟨A, B, hA, hB, hAB⟩ := hfinite Finset.univ
  refine ⟨A, B, hA, hB, eq_univ_of_univ_subset ?_⟩
  simpa only [Finset.mem_univ, iUnion_true, hcover] using hAB

end DifferentialGeometry.Topology
