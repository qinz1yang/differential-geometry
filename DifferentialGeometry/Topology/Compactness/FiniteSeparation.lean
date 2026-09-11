import Mathlib.Topology.Separation.Hausdorff

open Set

namespace DifferentialGeometry.Topology.Compactness

theorem exists_open_supersets_preserving_disjointness
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Finite ι]
    (K : ι → Set X) (hK : ∀ i, IsCompact (K i)) (R : ι → ι → Prop)
    (hR : ∀ i j, R i j → Disjoint (K i) (K j)) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧
      ∀ i j, R i j → Disjoint (U i) (U j) := by
  classical
  have hsep (i j : ι) : ∃ A B : Set X,
      IsOpen A ∧ IsOpen B ∧ K i ⊆ A ∧ K j ⊆ B ∧ (R i j → Disjoint A B) := by
    by_cases hij : R i j
    · obtain ⟨A, B, hA, hB, hi, hj, hd⟩ :=
        SeparatedNhds.of_isCompact_isCompact (hK i) (hK j) (hR i j hij)
      exact ⟨A, B, hA, hB, hi, hj, fun _ ↦ hd⟩
    · exact ⟨univ, univ, isOpen_univ, isOpen_univ, subset_univ _, subset_univ _,
        fun h ↦ (hij h).elim⟩
  choose A B hA hB hKA hKB hd using hsep
  let U (i : ι) := (⋂ j, A i j) ∩ (⋂ j, B j i)
  refine ⟨U, fun i ↦ (isOpen_iInter_of_finite (hA i)).inter
      (isOpen_iInter_of_finite fun j ↦ hB j i),
    fun i x hx ↦ ⟨mem_iInter.mpr fun j ↦ hKA i j hx,
      mem_iInter.mpr fun j ↦ hKB j i hx⟩, ?_⟩
  intro i j hij
  exact (hd i j hij).mono
    (fun _ hx ↦ mem_iInter.mp hx.1 j) (fun _ hx ↦ mem_iInter.mp hx.2 i)

end DifferentialGeometry.Topology.Compactness
