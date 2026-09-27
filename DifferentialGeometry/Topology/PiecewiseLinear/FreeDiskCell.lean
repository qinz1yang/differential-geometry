/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskDecomposition
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskSplit

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsPLDiskDecomposition.eq_biUnion_filter_of_union_inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) {C U V : Set E}
    (hC : C ∈ cells) (hunion : U ∪ V = K.space) (hinter : U ∩ V = C)
    (hside : ∀ E ∈ cells, E ⊆ U ∨ E ⊆ V) :
    U = ⋃ E ∈ cells.filter (fun E => E ⊆ U), E := by
  have hCU : C ⊆ U := hinter.symm.subset.trans inter_subset_left
  apply Subset.antisymm
  · intro x hx
    have hxK : x ∈ K.space := hunion ▸ Or.inl hx
    rw [h.space_eq] at hxK
    obtain ⟨E, hE, hxE⟩ := mem_iUnion₂.mp hxK
    rcases hside E hE with hEU | hEV
    · exact mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨hE, hEU⟩, hxE⟩
    · exact mem_iUnion₂.mpr ⟨C, Finset.mem_filter.mpr ⟨hC, hCU⟩,
        hinter.subset ⟨hx, hEV hxE⟩⟩
  · intro x hx
    obtain ⟨E, hE, hxE⟩ := mem_iUnion₂.mp hx
    exact (Finset.mem_filter.mp hE).2 hxE

private theorem exists_two_free_disk_cells_planar
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {cells : Finset (Set (EuclideanSpace ℝ (Fin 2)))}
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card) :
    ∃ C ∈ cells, ∃ D ∈ cells, C ≠ D ∧ IsFreeDiskCell K C ∧ IsFreeDiskCell K D := by
  classical
  induction cells using Finset.strongInductionOn generalizing K with
  | _ cells ih =>
    by_cases hall : ∀ C ∈ cells, (frontier K.space ∩ C).Nontrivial → IsFreeDiskCell K C
    · obtain ⟨C, hC, D, hD, hne, htrC, htrD⟩ := h.exists_two_cells_with_nontrivial_frontier_inter
        hmore
      exact ⟨C, hC, D, hD, hne, hall C hC htrC, hall D hD htrD⟩
    · push Not at hall
      obtain ⟨C, hC, htr, hnotfree⟩ := hall
      have htr' : (frontier C ∩ frontier K.space).Nontrivial := by
        rw [h.frontier_inter_cell hC, inter_comm] at htr
        exact htr
      obtain ⟨U, V, hU, hV, hunion, hinter, hUne, hVne, hCneU, hCneV, hfU, hfV, hsplit⟩ :=
        exists_isPLBall_pair_inter_eq_of_frontier_inter (h.cell_isPLBall C hC) h.isPLBall
          (h.cell_subset hC) htr' (h.not_frontier_cell_subset hmore hC)
          (mt (h.isFreeDiskCell_iff_isPLBall_frontier_inter hC).mpr hnotfree)
      have hCU : C ⊆ U := hinter.symm.subset.trans inter_subset_left
      have hCV : C ⊆ V := hinter.symm.subset.trans inter_subset_right
      have hUK : U ⊆ K.space := hunion ▸ subset_union_left
      have hVK : V ⊆ K.space := hunion ▸ subset_union_right
      have hside (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : E ∈ cells) : E ⊆ U ∨ E ⊆ V := by
        by_cases hEC : E = C
        · exact Or.inl (hEC.symm ▸ hCU)
        · exact hsplit E (h.cell_isPLBall E hE) (h.cell_subset hE)
            (h.disjoint_interior_cell hE hC hEC)
      let cellsU := cells.filter (fun E => E ⊆ U)
      let cellsV := cells.filter (fun E => E ⊆ V)
      have hcoverU : U = ⋃ E ∈ cellsU, E := h.eq_biUnion_filter_of_union_inter hC hunion hinter
          hside
      have hcoverV : V = ⋃ E ∈ cellsV, E := h.eq_biUnion_filter_of_union_inter hC
        ((union_comm V U).trans hunion) ((inter_comm V U).trans hinter) (fun E hE => (hside E
            hE).symm)
      have hsubU : cellsU ⊆ cells := Finset.filter_subset _ _
      have hsubV : cellsV ⊆ cells := Finset.filter_subset _ _
      have hdecU := h.restrict_cells hsubU hcoverU hU
      have hdecV := h.restrict_cells hsubV hcoverV hV
      have hspaceU : (restrict K U).space = U := hdecU.space_eq.trans hcoverU.symm
      have hspaceV : (restrict K V).space = V := hdecV.space_eq.trans hcoverV.symm
      have hbounds (W : Set (EuclideanSpace ℝ (Fin 2)))
          (hcover : W = ⋃ E ∈ cells.filter (fun E => E ⊆ W), E)
          (hCW : C ⊆ W) (hWne : W ≠ K.space) (hCne : C ≠ W) :
          1 < (cells.filter (fun E => E ⊆ W)).card ∧ cells.filter (fun E => E ⊆ W) ⊂ cells := by
        have hmem : C ∈ cells.filter (fun E => E ⊆ W) := Finset.mem_filter.mpr ⟨hC, hCW⟩
        constructor
        · apply lt_of_not_ge
          intro hsmall
          apply hCne
          apply Subset.antisymm hCW
          intro x hx
          rw [hcover] at hx
          obtain ⟨E, hE, hxE⟩ := mem_iUnion₂.mp hx
          exact (Finset.card_le_one.mp hsmall E hE C hmem) ▸ hxE
        · apply ssubset_iff_subset_ne.mpr
          refine ⟨Finset.filter_subset _ _, ?_⟩
          intro heq
          apply hWne
          rw [hcover, heq, ← h.space_eq]
      obtain ⟨hmoreU, hltU⟩ := hbounds U hcoverU hCU hUne hCneU
      obtain ⟨hmoreV, hltV⟩ := hbounds V hcoverV hCV hVne hCneV
      have hchoose (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
          (cs : Finset (Set (EuclideanSpace ℝ (Fin 2))))
          (hpair : ∃ A ∈ cs, ∃ B ∈ cs, A ≠ B ∧ IsFreeDiskCell L A ∧ IsFreeDiskCell L B) :
          ∃ E ∈ cs, E ≠ C ∧ IsFreeDiskCell L E := by
        obtain ⟨A, hA, B, hB, hne, hfA, hfB⟩ := hpair
        by_cases hAC : A = C
        · exact ⟨B, hB, hAC ▸ hne.symm, hfB⟩
        · exact ⟨A, hA, hAC, hfA⟩
      obtain ⟨E, hEU, hEC, hfreeE⟩ := hchoose _ _ (ih cellsU hltU hdecU hmoreU)
      obtain ⟨F, hFV, hFC, hfreeF⟩ := hchoose _ _ (ih cellsV hltV hdecV hmoreV)
      have hE : E ∈ cells := hsubU hEU
      have hF : F ∈ cells := hsubV hFV
      have hEU' : E ⊆ U := (Finset.mem_filter.mp hEU).2
      have hFV' : F ⊆ V := (Finset.mem_filter.mp hFV).2
      have hfreeE' : IsFreeDiskCell K E := h.isFreeDiskCell_of_frontier_subset_union
        hC hE hEC.symm hCU hEU' hUK hfU (by
          simpa only [hspaceU] using (hdecU.isFreeDiskCell_iff_isPLBall_frontier_inter hEU).mp
              hfreeE)
      have hfreeF' : IsFreeDiskCell K F := h.isFreeDiskCell_of_frontier_subset_union
        hC hF hFC.symm hCV hFV' hVK hfV (by
          simpa only [hspaceV] using (hdecV.isFreeDiskCell_iff_isPLBall_frontier_inter hFV).mp
              hfreeF)
      refine ⟨E, hE, F, hF, ?_, hfreeE', hfreeF'⟩
      intro heq
      apply h.not_cell_subset_cell hE hC hEC
      intro x hx
      exact hinter.subset ⟨hEU' hx, hFV' (heq ▸ hx)⟩

theorem IsPLDiskDecomposition.exists_two_free_disk_cells
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card) :
    ∃ C ∈ cells, ∃ D ∈ cells, C ≠ D ∧ IsFreeDiskCell K C ∧ IsFreeDiskCell K D := by
  classical
  obtain ⟨L, f, _, _, hL, hcard, hfree⟩ := h.exists_planar_image
  obtain ⟨A, hA, B, hB, hne, hfA, hfB⟩ :=
    exists_two_free_disk_cells_planar hL (hcard.symm ▸ hmore)
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hB
  exact ⟨C, hC, D, hD, fun heq => hne (heq ▸ rfl),
    (hfree C hC).mp hfA, (hfree D hD).mp hfB⟩

theorem IsPLDiskDecomposition.exists_free_disk_cell_ne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card) (C₀ : Set E) :
    ∃ C ∈ cells, C ≠ C₀ ∧ IsFreeDiskCell K C := by
  obtain ⟨C, hC, D, hD, hne, hfC, hfD⟩ := h.exists_two_free_disk_cells hmore
  by_cases hCC₀ : C = C₀
  · exact ⟨D, hD, hCC₀ ▸ hne.symm, hfD⟩
  · exact ⟨C, hC, hCC₀, hfC⟩

end DifferentialGeometry.Topology.PiecewiseLinear
