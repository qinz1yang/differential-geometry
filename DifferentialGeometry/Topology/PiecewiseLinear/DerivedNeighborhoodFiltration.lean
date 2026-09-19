/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.SimplicialComplex.FaceFiltration
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCellBoundary

/-! Finite filtrations of derived neighborhoods by actual face cells. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.SimplicialComplex
  (exists_face_enumeration_monotone_card geometricFacePrefix geometricFacePrefix_faces
    geometricFacePrefix_le geometricFacePrefix_last facePrefix facePrefix_zero facePrefix_le
    facePrefix_monotone facePrefix_succ_faces notMem_facePrefix_self mem_facePrefix_of_ssubset
    card_le_of_mem_facePrefix)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : Geometry.SimplicialComplex ℝ E) {m : ℕ} (e : Fin m ≃ K.faces)
  (he : Monotone fun i => (e i).val.card)

theorem geometricFacePrefix_succ (i : Fin m) :
    geometricFacePrefix K e he (i.val + 1) =
      subcomplexGeneratedBy K (insert (e i).val (geometricFacePrefix K e he i.val).faces) := by
  ext s
  rw [geometricFacePrefix_faces, facePrefix_succ_faces]
  constructor
  · rintro (rfl | hs)
    · exact ⟨(e i).val, ⟨(e i).property, Or.inl rfl⟩,
        Finset.Subset.refl _, K.nonempty_of_mem_faces (e i).property⟩
    · exact ⟨s, ⟨geometricFacePrefix_le K e he i.val hs, Or.inr hs⟩,
        Finset.Subset.refl _, (geometricFacePrefix K e he i.val).nonempty_of_mem_faces hs⟩
  · rintro ⟨t, ⟨_, ht⟩, hst, hs⟩
    rcases ht with rfl | ht
    · by_cases hsi : s = (e i).val
      · exact Or.inl hsi
      · exact Or.inr (mem_facePrefix_of_ssubset K.toPreAbstractSimplicialComplex e he i hs
          (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hsi⟩))
    · exact Or.inr ((geometricFacePrefix K e he i.val).down_closed ht hst hs)

open Classical in
theorem derivedNeighborhood_geometricFacePrefix_zero :
    (derivedNeighborhood K (geometricFacePrefix K e he 0)).space = ∅ := by
  classical
  rw [← iUnion_derivedNeighborhoodCell_space K _ (geometricFacePrefix_le K e he 0),
    geometricFacePrefix_faces, facePrefix_zero]
  change (⋃ s ∈ (∅ : Set (Finset E)), (derivedNeighborhoodCell K s).space) = ∅
  simp

open Classical in
theorem derivedNeighborhood_geometricFacePrefix_last :
    (derivedNeighborhood K (geometricFacePrefix K e he m)).space = K.space := by
  classical
  rw [geometricFacePrefix_last]
  refine Subset.antisymm (derivedNeighborhood_space_subset K K) ?_
  rw [← iUnion_derivedNeighborhoodCell_space K K Subset.rfl]
  exact space_subset_iUnion_derivedNeighborhoodCell_space K K Subset.rfl

open Classical in
theorem derivedNeighborhood_geometricFacePrefix_succ (i : Fin m) :
    (derivedNeighborhood K (geometricFacePrefix K e he (i.val + 1))).space =
      (derivedNeighborhood K (geometricFacePrefix K e he i.val)).space ∪
        (derivedNeighborhoodCell K (e i).val).space := by
  classical
  rw [geometricFacePrefix_succ, derivedNeighborhood_space_of_insert_face K _
    (geometricFacePrefix_le K e he i.val) (e i).property
    (fun _ ht hti => mem_facePrefix_of_ssubset K.toPreAbstractSimplicialComplex e he i ht hti)]
  exact union_comm _ _

open Classical in
theorem derivedNeighborhood_geometricFacePrefix_monotone :
    Monotone fun i => (derivedNeighborhood K (geometricFacePrefix K e he i)).space := by
  classical
  intro i j hij
  dsimp only
  rw [← iUnion_derivedNeighborhoodCell_space K _ (geometricFacePrefix_le K e he i),
    ← iUnion_derivedNeighborhoodCell_space K _ (geometricFacePrefix_le K e he j)]
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion₂.mpr ⟨s, facePrefix_monotone K.toPreAbstractSimplicialComplex e he hij hs, hxs⟩

open Classical in
theorem exists_derivedNeighborhood_filtration [FiniteDimensional ℝ E] [Finite K.faces]
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) :
    ∃ m : ℕ, ∃ e : Fin m ≃ K.faces, ∃ he : Monotone (fun i => (e i).val.card),
      let L := geometricFacePrefix K e he
      let N := fun i => derivedNeighborhood K (L i)
      (N 0).space = ∅ ∧ (N m).space = K.space ∧ Monotone (fun i => (N i).space) ∧
        (∀ i, IsCombinatorialManifoldWithBoundary (n + 2) (N i)) ∧
        ∀ i : Fin m, (e i).val ∉ (L i.val).faces ∧
          (∀ t : Finset E, t.Nonempty → t ⊂ (e i).val → t ∈ (L i.val).faces) ∧
          (∀ t ∈ (L i.val).faces, t.card ≤ (e i).val.card) ∧
          L (i.val + 1) = subcomplexGeneratedBy K (insert (e i).val (L i.val).faces) ∧
          (N (i.val + 1)).space = (N i.val).space ∪ (derivedNeighborhoodCell K (e i).val).space ∧
          (derivedNeighborhoodCell K (e i).val).space ∩ (N i.val).space ⊆
            (boundaryComplex (n + 2) (N i.val)).space := by
  classical
  obtain ⟨m, e, he⟩ := exists_face_enumeration_monotone_card K.toPreAbstractSimplicialComplex
  refine ⟨m, e, he, derivedNeighborhood_geometricFacePrefix_zero K e he,
    derivedNeighborhood_geometricFacePrefix_last K e he,
    derivedNeighborhood_geometricFacePrefix_monotone K e he,
    fun i => hK.derivedNeighborhood _, ?_⟩
  intro i
  have hnot := notMem_facePrefix_self K.toPreAbstractSimplicialComplex e he i
  exact ⟨hnot,
    fun _ ht hti => mem_facePrefix_of_ssubset K.toPreAbstractSimplicialComplex e he i ht hti,
    fun _ ht => card_le_of_mem_facePrefix K.toPreAbstractSimplicialComplex e he i ht,
    geometricFacePrefix_succ K e he i, derivedNeighborhood_geometricFacePrefix_succ K e he i,
    derivedNeighborhoodCell_inter_subset_boundary_derivedNeighborhood K _ hK
      (geometricFacePrefix_le K e he i.val) (e i).property hnot⟩

end DifferentialGeometry.Topology.PiecewiseLinear
