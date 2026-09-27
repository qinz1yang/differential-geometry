/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCellDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCover

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsFreeDiskCellDeletion.triangle_data
    {D : Set E} {P Q : Geometry.SimplicialComplex ℝ E × Finset (Set E)}
    (h : IsFreeDiskCellDeletion D P Q)
    (htriangles : ∀ C ∈ P.2, ∃ t ∈ P.1.faces, t.card = 3 ∧
      C = convexHull ℝ (t : Set E)) :
    IsPLDiskDecomposition Q.1 Q.2 ∧
      (∀ C ∈ Q.2, ∃ t ∈ Q.1.faces, t.card = 3 ∧ C = convexHull ℝ (t : Set E)) ∧
      ∃ t ∈ P.1.faces, t.card = 3 ∧ ¬convexHull ℝ (t : Set E) ⊆ D ∧
        IsPLBall 1 (convexHull ℝ (t : Set E) ∩ (boundaryComplex 2 P.1).space) ∧
        Q.1.space = closure (P.1.space \ convexHull ℝ (t : Set E)) := by
  obtain ⟨hP, C, hC, hnot, hfree, hcomplex, hcells⟩ := h
  have hQ := hP.erase_of_isFreeDiskCell hC hfree
  have hcover := hP.closure_sdiff_cell_eq_biUnion_erase hC
  have hspace : (restrict P.1 (closure (P.1.space \ C))).space =
      closure (P.1.space \ C) := hQ.space_eq.trans hcover.symm
  have hremaining : ∀ F ∈ P.2.erase C, ∃ t ∈
      (restrict P.1 (closure (P.1.space \ C))).faces,
      t.card = 3 ∧ F = convexHull ℝ (t : Set E) := by
    intro F hF
    obtain ⟨t, ht, hcard, rfl⟩ := htriangles F (Finset.mem_of_mem_erase hF)
    refine ⟨t, ⟨ht, ?_⟩, hcard, rfl⟩
    rw [hcover]
    exact subset_iUnion_of_subset _ (subset_iUnion_of_subset hF Subset.rfl)
  obtain ⟨t, ht, hcard, rfl⟩ := htriangles C hC
  refine ⟨by simpa only [hcomplex, hcells] using hQ,
    by simpa only [hcomplex, hcells] using hremaining, t, ht, hcard, hnot, ?_, ?_⟩
  · exact (hP.isFreeDiskCell_iff_isPLBall_inter_boundaryComplex hC).mp hfree
  · exact hcomplex ▸ hspace

open Classical in
theorem IsPLBall.exists_triangular_deletion_sequence_to_subdisk
    {B D : Set E} (hB : IsPLBall 2 B) (hD : IsPLBall 2 D) (hDB : D ⊆ B) :
    ∃ (K L : Geometry.SimplicialComplex ℝ E) (cells subcells cs : Finset (Set E)),
      K.faces.Finite ∧ K.space = B ∧
      (∀ C ∈ cells, ∃ t ∈ K.faces, t.card = 3 ∧ C = convexHull ℝ (t : Set E)) ∧
      IsPLDiskDecomposition K cells ∧
      subcells ⊆ cells ∧ D = ⋃ C ∈ subcells, C ∧
      IsPLDiskDecomposition L cs ∧ L.space = D ∧ subcells ⊆ cs ∧ cs ⊆ cells ∧
      Relation.ReflTransGen (IsFreeDiskCellDeletion D) (K, cells) (L, cs) := by
  obtain ⟨R₀, hR₀fin, hR₀B⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  obtain ⟨R, hRR₀, hRfin, hRD⟩ := exists_isSubdivision_restrict_space R₀
    hD.isPolyhedron (hDB.trans hR₀B.symm.subset)
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite (restrict R D).faces := (restrict_faces_finite R D).to_subtype
  have hRB : R.space = B := hRR₀.space_eq.trans hR₀B
  have hRball : IsPLBall 2 R.space := hRB.symm ▸ hB
  have hRDball : IsPLBall 2 (restrict R D).space := hRD.symm ▸ hD
  let ts := hRfin.toFinset.filter (fun t => t.card = 3)
  let cells := ts.image (fun t : Finset E => convexHull ℝ (t : Set E))
  let subcells := cells.filter (fun C => C ⊆ D)
  have htmem (t : Finset E) : t ∈ ts ↔ t ∈ R.faces ∧ t.card = 3 := by
    simp only [ts, Finset.mem_filter, Set.Finite.mem_toFinset]
  have hcells (C : Set E) : C ∈ cells ↔
      ∃ t ∈ R.faces, t.card = 3 ∧ C = convexHull ℝ (t : Set E) := by
    simp only [cells, Finset.mem_image, htmem]
    aesop
  have hcellball (C : Set E) (hC : C ∈ cells) : IsPLBall 2 C := by
    obtain ⟨t, ht, hcard, rfl⟩ := (hcells C).mp hC
    exact isPLBall_convexHull_of_affineIndependent t (R.indep ht) hcard
  have hcover : B = ⋃ C ∈ cells, C := by
    rw [← hRB]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := R.mem_space_iff.mp hx
      obtain ⟨t, ht, hst, hcard⟩ := exists_face_superset_card_eq_of_isPLBall R hRball hs
      exact mem_iUnion₂.mpr ⟨_, (hcells _).mpr ⟨t, ht, hcard, rfl⟩,
        convexHull_mono (Finset.coe_subset.mpr hst) hxs⟩
    · intro x hx
      obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
      obtain ⟨t, ht, _, rfl⟩ := (hcells C).mp hC
      exact R.convexHull_subset_space ht hxC
  have hDcover : D = ⋃ C ∈ subcells, C := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := (restrict R D).mem_space_iff.mp (hRD.symm ▸ hx)
      obtain ⟨t, ht, hst, hcard⟩ :=
        exists_face_superset_card_eq_of_isPLBall (restrict R D) hRDball hs
      refine mem_iUnion₂.mpr ⟨_, Finset.mem_filter.mpr
        ⟨(hcells _).mpr ⟨t, ht.1, hcard, rfl⟩, ht.2⟩, ?_⟩
      exact convexHull_mono (Finset.coe_subset.mpr hst) hxs
    · intro x hx
      obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
      exact (Finset.mem_filter.mp hC).2 hxC
  have hinter (C : Set E) (hC : C ∈ cells) (F : Set E) (hF : F ∈ cells)
      (hCF : C ≠ F) (hmeet : (C ∩ F).Nonempty) :
      IsPLBall 0 (C ∩ F) ∨ IsPLBall 1 (C ∩ F) := by
    obtain ⟨t, ht, htcard, rfl⟩ := (hcells C).mp hC
    obtain ⟨u, hu, hucard, rfl⟩ := (hcells F).mp hF
    rw [R.convexHull_inter_convexHull ht hu, ← Finset.coe_inter] at hmeet ⊢
    have htu : t ≠ u := fun h => hCF (h ▸ rfl)
    have hlt : (t ∩ u).card < t.card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro heq
      have hsub : t ⊆ u := heq ▸ Finset.inter_subset_right
      exact htu (Finset.eq_of_subset_of_card_le hsub (by omega))
    have hpos : 0 < (t ∩ u).card := by
      apply Finset.card_pos.mpr
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.coe_empty,
        convexHull_empty] at hmeet
      exact Set.not_nonempty_empty hmeet
    have hind := affineIndependent_of_subset (τ := t ∩ u) (R.indep ht)
      Finset.inter_subset_left
    rcases (show (t ∩ u).card = 1 ∨ (t ∩ u).card = 2 by omega) with hc | hc
    · exact Or.inl (isPLBall_convexHull_of_affineIndependent _ hind hc)
    · exact Or.inr (isPLBall_convexHull_of_affineIndependent _ hind hc)
  obtain ⟨K, _, hKB, hK⟩ :=
    exists_isPLDiskDecomposition_of_cover hB cells hcellball hcover hinter
  have hKR : IsPLHomeomorphOn (id : E → E) K.space R.space := by
    rw [hKB, hRB]
    exact hB.isPolyhedron.isPLHomeomorphOn_id
  have hcellR (C : Set E) (hC : C ∈ cells) : (restrict R (id '' C)).space = id '' C := by
    rw [image_id]
    obtain ⟨t, ht, _, rfl⟩ := (hcells C).mp hC
    exact restrict_convexHull_space ht
  have hR : IsPLDiskDecomposition R cells := by
    simpa only [image_id, Finset.image_id'] using hK.image hRfin hKR hcellR
  have hsub : subcells ⊆ cells := Finset.filter_subset _ _
  obtain ⟨L, cs, hL, hLD, hsubcs, hcscells, hsequence⟩ :=
    hR.exists_free_disk_cell_deletion_sequence hsub hD hDcover
  exact ⟨R, L, cells, subcells, cs, hRfin, hRB, fun C hC => (hcells C).mp hC,
    hR, hsub, hDcover, hL, hLD, hsubcs, hcscells, hsequence⟩

end DifferentialGeometry.Topology.PiecewiseLinear
