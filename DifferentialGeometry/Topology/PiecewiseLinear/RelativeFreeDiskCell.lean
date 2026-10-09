/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FreeDiskCell
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_cell_not_subset_with_nontrivial_frontier_inter
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {cells : Finset (Set (EuclideanSpace ℝ (Fin 2)))} (h : IsPLDiskDecomposition K cells)
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsClosed D) (hnot : ¬frontier K.space ⊆ D) :
    ∃ C ∈ cells, ¬C ⊆ D ∧ (frontier K.space ∩ C).Nontrivial := by
  classical
  by_contra hnone
  let cs := cells.filter (fun C => ¬C ⊆ D)
  have hfinite (C : Set (EuclideanSpace ℝ (Fin 2))) (hC : C ∈ cs) :
      (frontier K.space ∩ C).Finite :=
    (Set.not_nontrivial_iff.mp fun htr =>
      hnone ⟨C, (Finset.mem_filter.mp hC).1, (Finset.mem_filter.mp hC).2, htr⟩).finite
  let F := ⋃ C ∈ cs, frontier K.space ∩ C
  have hF : F.Finite := Set.Finite.biUnion cs.finite_toSet hfinite
  have hsub : frontier K.space \ F ⊆ D := by
    intro x hx
    have hxK := h.isPLBall.isPolyhedron.isClosed.frontier_subset hx.1
    rw [h.space_eq] at hxK
    obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hxK
    by_cases hCD : C ⊆ D
    · exact hCD hxC
    · exact (hx.2 (mem_iUnion₂.mpr ⟨C, Finset.mem_filter.mpr ⟨hC, hCD⟩, hx.1, hxC⟩)).elim
  obtain ⟨J, hJ⟩ := exists_polygonalCircle_of_isPLSphere_one h.isPLBall.isPLSphere_frontier
  apply hnot
  intro x hx
  apply closure_minimal hsub hD
  rw [← hJ]
  exact J.carrier_subset_closure_sdiff_finite hF (hJ.symm ▸ hx)

private theorem exists_free_disk_cell_not_subset_planar
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {cells subcells : Finset (Set (EuclideanSpace ℝ (Fin 2)))}
    (h : IsPLDiskDecomposition K cells) (hsub : subcells ⊆ cells)
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsPLBall 2 D)
    (hcover : D = ⋃ C ∈ subcells, C) (hne : D ≠ K.space) :
    ∃ C ∈ cells, ¬C ⊆ D ∧ IsFreeDiskCell K C := by
  classical
  have hDK : D ⊆ K.space := by
    rw [hcover]
    exact iUnion₂_subset fun C hC => h.cell_subset (hsub hC)
  have hCD (C : Set (EuclideanSpace ℝ (Fin 2))) (hC : C ∈ subcells) : C ⊆ D := by
    rw [hcover]
    exact subset_iUnion_of_subset C (subset_iUnion_of_subset hC Subset.rfl)
  obtain ⟨C, hC, hnotCD, htr⟩ := exists_cell_not_subset_with_nontrivial_frontier_inter h
    hD.isPolyhedron.isClosed (fun hbd => hne (hD.eq_of_subset_of_frontier_subset h.isPLBall hDK
        hbd))
  by_cases hfree : IsFreeDiskCell K C
  · exact ⟨C, hC, hnotCD, hfree⟩
  have hmore : 1 < cells.card := by
    apply lt_of_not_ge
    intro hsmall
    obtain ⟨p, hp⟩ := hD.nonempty
    rw [hcover] at hp
    obtain ⟨A, hA, _⟩ := mem_iUnion₂.mp hp
    exact hnotCD ((Finset.card_le_one.mp hsmall C hC A (hsub hA)).symm ▸ hCD A hA)
  have htr' : (frontier C ∩ frontier K.space).Nontrivial := by
    rw [h.frontier_inter_cell hC, inter_comm] at htr
    exact htr
  obtain ⟨U, V, hU, hV, hunion, hinter, _, _, hCneU, hCneV, hfU, hfV, hsplit⟩ :=
    exists_isPLBall_pair_inter_eq_of_frontier_inter (h.cell_isPLBall C hC) h.isPLBall
      (h.cell_subset hC) htr' (h.not_frontier_cell_subset hmore hC)
      (mt (h.isFreeDiskCell_iff_isPLBall_frontier_inter hC).mpr hfree)
  have hCU : C ⊆ U := hinter.symm.subset.trans inter_subset_left
  have hCV : C ⊆ V := hinter.symm.subset.trans inter_subset_right
  have hdisCD : Disjoint (interior C) D := by
    rw [disjoint_left]
    intro p hpC hpD
    rw [hcover] at hpD
    obtain ⟨A, hA, hpA⟩ := mem_iUnion₂.mp hpD
    have hCA : C ≠ A := fun heq => hnotCD (heq.symm ▸ hCD A hA)
    exact disjoint_left.mp (h.disjoint_interior_cell hC (hsub hA) hCA) hpC hpA
  have hdisDC : Disjoint (interior D) C := by
    have hsub' : interior C ⊆ (interior D)ᶜ := fun p hpC hpD =>
      disjoint_left.mp hdisCD hpC (interior_subset hpD)
    have hsub'' := closure_minimal hsub' isOpen_interior.isClosed_compl
    rw [(h.cell_isPLBall C hC).closure_interior] at hsub''
    exact disjoint_left.mpr fun p hpD hpC => hsub'' hpC hpD
  have hside (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : A ∈ cells) : A ⊆ U ∨ A ⊆ V := by
    by_cases hAC : A = C
    · exact Or.inl (hAC.symm ▸ hCU)
    · exact hsplit A (h.cell_isPLBall A hA) (h.cell_subset hA)
        (h.disjoint_interior_cell hA hC hAC)
  have hfinish (U V : Set (EuclideanSpace ℝ (Fin 2))) (hU : IsPLBall 2 U)
      (hunion : U ∪ V = K.space) (hinter : U ∩ V = C) (hCneU : C ≠ U)
      (hfU : frontier U ⊆ frontier K.space ∪ C) (hDV : D ⊆ V)
      (hside : ∀ A ∈ cells, A ⊆ U ∨ A ⊆ V) :
      ∃ A ∈ cells, ¬A ⊆ D ∧ IsFreeDiskCell K A := by
    have hCU : C ⊆ U := hinter.symm.subset.trans inter_subset_left
    have hUK : U ⊆ K.space := hunion ▸ subset_union_left
    let cs := cells.filter (fun A => A ⊆ U)
    have hcoverU : U = ⋃ A ∈ cs, A := h.eq_biUnion_filter_of_union_inter hC hunion hinter hside
    have hcs : cs ⊆ cells := Finset.filter_subset _ _
    have hdec := h.restrict_cells hcs hcoverU hU
    have hspace : (restrict K U).space = U := hdec.space_eq.trans hcoverU.symm
    have hCcs : C ∈ cs := Finset.mem_filter.mpr ⟨hC, hCU⟩
    have hmoreU : 1 < cs.card := by
      apply lt_of_not_ge
      intro hsmall
      apply hCneU
      apply Subset.antisymm hCU
      intro p hp
      rw [hcoverU] at hp
      obtain ⟨A, hA, hpA⟩ := mem_iUnion₂.mp hp
      exact (Finset.card_le_one.mp hsmall A hA C hCcs) ▸ hpA
    obtain ⟨A, hA, hAC, hfreeA⟩ := hdec.exists_free_disk_cell_ne hmoreU C
    have hAU : A ⊆ U := (Finset.mem_filter.mp hA).2
    refine ⟨A, hcs hA, ?_, ?_⟩
    · intro hAD
      exact h.not_cell_subset_cell (hcs hA) hC hAC fun p hp =>
        hinter ▸ ⟨hAU hp, hDV (hAD hp)⟩
    · apply h.isFreeDiskCell_of_frontier_subset_union hC (hcs hA) hAC.symm
        hCU hAU hUK hfU
      simpa only [hspace] using (hdec.isFreeDiskCell_iff_isPLBall_frontier_inter hA).mp hfreeA
  rcases hsplit D hD hDK hdisDC with hDU | hDV
  · exact hfinish V U hV ((union_comm V U).trans hunion) ((inter_comm V U).trans hinter)
      hCneV hfV hDU (fun A hA => (hside A hA).symm)
  · exact hfinish U V hU hunion hinter hCneU hfU hDV hside

theorem IsPLDiskDecomposition.exists_free_disk_cell_not_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {cells subcells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) (hsub : subcells ⊆ cells)
    {D : Set E} (hD : IsPLBall 2 D) (hcover : D = ⋃ C ∈ subcells, C) (hne : D ≠ K.space) :
    ∃ C ∈ cells, ¬C ⊆ D ∧ IsFreeDiskCell K C := by
  classical
  have hDK : D ⊆ K.space := by
    rw [hcover]
    exact iUnion₂_subset fun C hC => h.cell_subset (hsub hC)
  obtain ⟨L, f, _, hf, hL, _, hfree⟩ := h.exists_planar_image
  have hD' := hD.of_isPLHomeomorphOn (hf.restrict hD.isPolyhedron hDK)
  have hcover' : f '' D = ⋃ C ∈ subcells.image (fun C => f '' C), C := by
    rw [hcover]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨f '' C, Finset.mem_image.mpr ⟨C, hC, rfl⟩, x, hxC, rfl⟩
    · intro hy
      obtain ⟨A, hA, hyA⟩ := mem_iUnion₂.mp hy
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨x, hx, rfl⟩ := hyA
      exact ⟨x, mem_iUnion₂.mpr ⟨C, hC, hx⟩, rfl⟩
  have hne' : f '' D ≠ L.space := fun heq => hne
    ((hf.bijOn.injOn.image_eq_image_iff hDK Subset.rfl).mp (heq.trans hf.image_eq.symm))
  obtain ⟨A, hA, hnot, hfreeA⟩ := exists_free_disk_cell_not_subset_planar hL
    (Finset.image_subset_image hsub) hD' hcover' hne'
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hA
  exact ⟨C, hC, fun hCD => hnot (image_mono hCD), (hfree C hC).mp hfreeA⟩

end DifferentialGeometry.Topology.PiecewiseLinear
