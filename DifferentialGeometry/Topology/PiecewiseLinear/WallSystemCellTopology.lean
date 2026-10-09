/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.WallSystemBlocks
import DifferentialGeometry.Topology.PiecewiseLinear.Barycentric
import DifferentialGeometry.Topology.PiecewiseLinear.Derived

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

def wallSystemStar (Q : Geometry.SimplicialComplex ℝ Ea) (ρ : M → Ea) (s : Finset Ea) :
    Set M :=
  ρ ⁻¹' (⋃ t ∈ {t : Finset Ea | t ∈ Q.faces ∧ ¬s ⊆ t}, convexHull ℝ (t : Set Ea))ᶜ

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCellInt_subset_wallSystemCell (ρ : M → Ea) (s : Finset Ea) :
    wallSystemCellInt ρ s ⊆ wallSystemCell ρ s :=
  fun _ hx => openSimplex_subset_convexHull s hx

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isClosed_wallSystemCell {ρ : M → Ea} (hcont : Continuous ρ) (s : Finset Ea) :
    IsClosed (wallSystemCell ρ s) :=
  (s.finite_toSet.isClosed_convexHull ℝ).preimage hcont

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCell_subset_wallSystemSkeleton {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {s : Finset Ea} (hs : s ∈ Q.faces) (hcard : s.card ≤ 2) :
    wallSystemCell ρ s ⊆ wallSystemSkeleton Q ρ :=
  fun _ hx => mem_iUnion₂.2 ⟨s, ⟨hs, hcard⟩, hx⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isClosed_wallSystemSkeleton {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hfin : Q.faces.Finite) (hcont : Continuous ρ) : IsClosed (wallSystemSkeleton Q ρ) :=
  Set.Finite.isClosed_biUnion (hfin.subset fun _ ht => ht.1)
    fun t _ => isClosed_wallSystemCell hcont t

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem disjoint_wallSystemCellInt_wallSystemSkeleton {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    Disjoint (wallSystemCellInt ρ c) (wallSystemSkeleton Q ρ) := by
  refine Set.disjoint_left.2 fun x hx hskel => ?_
  obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hskel
  have hsub : c ⊆ t :=
    face_subset_of_mem_openSimplex_of_mem_convexHull Q hc.1 ht.1 hx hxt
  have hle := Finset.card_le_card hsub
  have hc4 : c.card = 4 := hc.2
  have ht2 : t.card ≤ 2 := ht.2
  omega

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCellInt_nonempty {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hrange : Set.range ρ = Q.space) {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    (wallSystemCellInt ρ c).Nonempty := by
  have hne : c.Nonempty := Finset.card_pos.mp (by rw [hc.2]; norm_num)
  have hmem : c.centroid ℝ id ∈ Q.space :=
    Q.convexHull_subset_space hc.1 (openSimplex_subset_convexHull c
      (centroid_mem_openSimplex hne))
  rw [← hrange] at hmem
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, by simpa only [wallSystemCellInt, mem_preimage, hx] using
    centroid_mem_openSimplex hne⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemSkeleton_ne_univ {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hrange : Set.range ρ = Q.space) {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    wallSystemSkeleton Q ρ ≠ univ := by
  intro huniv
  obtain ⟨x, hx⟩ := wallSystemCellInt_nonempty (ρ := ρ) hrange hc
  have hx' : x ∈ wallSystemSkeleton Q ρ := by rw [huniv]; exact mem_univ x
  exact Set.disjoint_left.1 (disjoint_wallSystemCellInt_wallSystemSkeleton hc) hx hx'

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem iUnion_wallSystemCell_eq_univ {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hrange : Set.range ρ = Q.space)
    (hmem : ∀ s ∈ Q.faces, ∃ c ∈ wallSystemCells Q, s ⊆ c) :
    (⋃ c ∈ wallSystemCells Q, wallSystemCell ρ c) = univ := by
  refine eq_univ_of_forall fun x => ?_
  have hx : ρ x ∈ Q.space := by rw [← hrange]; exact mem_range_self x
  obtain ⟨s, hs, hxs⟩ := Q.mem_space_iff.mp hx
  obtain ⟨c, hc, hsc⟩ := hmem s hs
  exact mem_iUnion₂.2 ⟨c, hc, convexHull_mono (Finset.coe_subset.2 hsc) hxs⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem disjoint_wallSystemCellInt_wallSystemCell {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {c c' : Finset Ea} (hc : c ∈ wallSystemCells Q)
    (hc' : c' ∈ wallSystemCells Q) (hne : c ≠ c') :
    Disjoint (wallSystemCellInt ρ c) (wallSystemCell ρ c') := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  refine hne (Finset.eq_of_subset_of_card_le
    (face_subset_of_mem_openSimplex_of_mem_convexHull Q hc.1 hc'.1 hx hx') ?_)
  have hc4 : c.card = 4 := hc.2
  have hc4' : c'.card = 4 := hc'.2
  omega

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCell_sdiff_subset_iUnion_wall {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    wallSystemCell ρ c \ wallSystemCellInt ρ c ⊆
      ⋃ w ∈ wallSystemWalls Q, wallSystemCell ρ w := by
  rintro x ⟨hx, hxi⟩
  obtain ⟨t, htc, htne, hxt⟩ := exists_openSimplex_of_mem_convexHull hx
  have hc4 : c.card = 4 := hc.2
  have hle : t.card ≤ c.card := Finset.card_le_card htc
  have hcard : t.card ≤ 3 := by
    by_contra hlt
    have heq : t = c := Finset.eq_of_subset_of_card_le htc (by omega)
    exact hxi (by rw [wallSystemCellInt, mem_preimage, ← heq]; exact hxt)
  obtain ⟨w, htw, hwc, hwcard⟩ := Finset.exists_subsuperset_card_eq htc hcard (by omega)
  refine mem_iUnion₂.2 ⟨w, ⟨Q.down_closed hc.1 hwc (Finset.card_pos.mp (by omega)),
    hwcard⟩, ?_⟩
  exact convexHull_mono (Finset.coe_subset.2 htw) (openSimplex_subset_convexHull t hxt)

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCell_sdiff_subset_wallSystemSkeleton {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {w : Finset Ea} (hw : w ∈ wallSystemWalls Q) :
    wallSystemCell ρ w \ wallSystemCellInt ρ w ⊆ wallSystemSkeleton Q ρ := by
  rintro x ⟨hx, hxi⟩
  obtain ⟨t, htw, htne, hxt⟩ := exists_openSimplex_of_mem_convexHull hx
  have hw3 : w.card = 3 := hw.2
  have hle : t.card ≤ w.card := Finset.card_le_card htw
  have hcard : t.card ≤ 2 := by
    by_contra hlt
    have heq : t = w := Finset.eq_of_subset_of_card_le htw (by omega)
    exact hxi (by rw [wallSystemCellInt, mem_preimage, ← heq]; exact hxt)
  exact mem_iUnion₂.2 ⟨t, ⟨Q.down_closed hw.1 htw htne, hcard⟩,
    openSimplex_subset_convexHull t hxt⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCell_inter_subset_wallSystemSkeleton {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {w w' : Finset Ea} (hw : w ∈ wallSystemWalls Q)
    (hw' : w' ∈ wallSystemWalls Q) (hne : w ≠ w') :
    wallSystemCell ρ w ∩ wallSystemCell ρ w' ⊆ wallSystemSkeleton Q ρ := by
  classical
  rintro x ⟨hx, hx'⟩
  have hw3 : w.card = 3 := hw.2
  have hw3' : w'.card = 3 := hw'.2
  have hmem : ρ x ∈ convexHull ℝ ((w ∩ w' : Finset Ea) : Set Ea) := by
    rw [Finset.coe_inter]
    exact Q.inter_subset_convexHull hw.1 hw'.1 ⟨hx, hx'⟩
  have hnonempty : (w ∩ w').Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hmem
    simp at hmem
  have hle : (w ∩ w').card ≤ w.card := Finset.card_le_card Finset.inter_subset_left
  have hcard : (w ∩ w').card ≤ 2 := by
    by_contra hlt
    have hww : w ∩ w' = w :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hsub : w ⊆ w' := hww ▸ Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))
  exact mem_iUnion₂.2 ⟨w ∩ w',
    ⟨Q.down_closed hw.1 Finset.inter_subset_left hnonempty, hcard⟩, hmem⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isOpen_wallSystemStar {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hfin : Q.faces.Finite) (hcont : Continuous ρ) (s : Finset Ea) :
    IsOpen (wallSystemStar Q ρ s) := by
  refine IsOpen.preimage hcont (isOpen_compl_iff.mpr ?_)
  exact Set.Finite.isClosed_biUnion (hfin.subset fun _ ht => ht.1)
    fun t _ => t.finite_toSet.isClosed_convexHull ℝ

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCellInt_subset_wallSystemStar {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {s : Finset Ea} (hs : s ∈ Q.faces) :
    wallSystemCellInt ρ s ⊆ wallSystemStar Q ρ s := by
  intro x hx hbad
  obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hbad
  exact ht.2 (face_subset_of_mem_openSimplex_of_mem_convexHull Q hs ht.1 hx hxt)

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem exists_face_of_mem_wallSystemStar {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} (hrange : Set.range ρ = Q.space) {s : Finset Ea} {x : M}
    (hx : x ∈ wallSystemStar Q ρ s) :
    ∃ t ∈ Q.faces, s ⊆ t ∧ x ∈ wallSystemCellInt ρ t := by
  have hxQ : ρ x ∈ Q.space := by rw [← hrange]; exact mem_range_self x
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex Q hxQ
  refine ⟨t, ht, ?_, hxt⟩
  by_contra hst
  exact hx (mem_iUnion₂.2 ⟨t, ⟨ht, hst⟩, openSimplex_subset_convexHull t hxt⟩)

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCellInt_eq_wallSystemStar {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} (hrange : Set.range ρ = Q.space) (hdim : ∀ t ∈ Q.faces, t.card ≤ 4)
    {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    wallSystemCellInt ρ c = wallSystemStar Q ρ c := by
  refine Subset.antisymm (wallSystemCellInt_subset_wallSystemStar hc.1) fun x hx => ?_
  obtain ⟨t, ht, hct, hxt⟩ := exists_face_of_mem_wallSystemStar hrange hx
  have hc4 : c.card = 4 := hc.2
  have hdt := hdim t ht
  rw [Finset.eq_of_subset_of_card_le hct (by omega)]
  exact hxt

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isOpen_wallSystemCellInt {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hfin : Q.faces.Finite) (hcont : Continuous ρ) (hrange : Set.range ρ = Q.space)
    (hdim : ∀ t ∈ Q.faces, t.card ≤ 4) {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    IsOpen (wallSystemCellInt ρ c) := by
  rw [wallSystemCellInt_eq_wallSystemStar hrange hdim hc]
  exact isOpen_wallSystemStar hfin hcont c

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemStar_inter_wall_subset {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} (hrange : Set.range ρ = Q.space) {w w' : Finset Ea}
    (hw : w ∈ wallSystemWalls Q) (hw' : w' ∈ wallSystemWalls Q) :
    wallSystemStar Q ρ w ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w := by
  rintro x ⟨hxs, hx'⟩
  obtain ⟨t, ht, hwt, hxt⟩ := exists_face_of_mem_wallSystemStar hrange hxs
  have htw' : t ⊆ w' :=
    face_subset_of_mem_openSimplex_of_mem_convexHull Q ht hw'.1 hxt hx'
  have hw3 : w.card = 3 := hw.2
  have hw3' : w'.card = 3 := hw'.2
  rw [Finset.eq_of_subset_of_card_le (hwt.trans htw') (by omega)]
  exact hx'

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemStar_subset_union_wallSystemCell {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} (hrange : Set.range ρ = Q.space)
    (hmem : ∀ s ∈ Q.faces, ∃ c ∈ wallSystemCells Q, s ⊆ c) {w cm cp : Finset Ea}
    (hsides : ∀ c ∈ wallSystemCells Q, w ⊆ c → c = cm ∨ c = cp) :
    wallSystemStar Q ρ w ⊆ wallSystemCell ρ cm ∪ wallSystemCell ρ cp := by
  intro x hx
  obtain ⟨t, ht, hwt, hxt⟩ := exists_face_of_mem_wallSystemStar hrange hx
  obtain ⟨c, hc, htc⟩ := hmem t ht
  have hxc : x ∈ wallSystemCell ρ c :=
    convexHull_mono (Finset.coe_subset.2 htc) (openSimplex_subset_convexHull t hxt)
  rcases hsides c hc (hwt.trans htc) with rfl | rfl
  · exact Or.inl hxc
  · exact Or.inr hxc

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCell_subset_layer {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {ι : Type} {Eb Eb' : ι → Set M} (i : ι)
    (hstar : ∀ c ∈ wallSystemCells Q, (wallSystemCell ρ c ∩ Eb i).Nonempty →
      wallSystemCell ρ c ⊆ Eb' i)
    (hmem : ∀ s ∈ Q.faces, ∃ c ∈ wallSystemCells Q, s ⊆ c) {s : Finset Ea}
    (hs : s ∈ Q.faces) (hne : (wallSystemCell ρ s ∩ Eb i).Nonempty) :
    wallSystemCell ρ s ⊆ Eb' i := by
  obtain ⟨c, hc, hsc⟩ := hmem s hs
  have hsub : wallSystemCell ρ s ⊆ wallSystemCell ρ c :=
    fun _ hx => convexHull_mono (Finset.coe_subset.2 hsc) hx
  obtain ⟨z, hzs, hzE⟩ := hne
  exact hsub.trans (hstar c hc ⟨z, hsub hzs, hzE⟩)

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem subset_iUnion_wallSystemCell_of_eq_boundary {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {Bf : Set (Finset Ea)} {BdM : Set M} (hfaces : Bf ⊆ wallSystemWalls Q)
    (heq : BdM = ⋃ w ∈ Bf, wallSystemCell ρ w) :
    BdM ⊆ ⋃ w ∈ wallSystemWalls Q, wallSystemCell ρ w := by
  rw [heq]
  exact iUnion₂_subset fun w hw x hx => mem_iUnion₂.2 ⟨w, hfaces hw, hx⟩

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
