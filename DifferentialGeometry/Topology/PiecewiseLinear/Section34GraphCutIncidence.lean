/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ControlledVertexCells

open Set Function Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M}

noncomputable def section34GraphSplitCell (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U)
    (e : Section34EdgeIndex 𝒦 𝒦') : Set M := by
  classical
  exact 𝒦'.map '' (splittingDisk 𝒦'.complex e.1 e.2.1).space

noncomputable def section34GraphSplitBoundary (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U)
    (e : Section34EdgeIndex 𝒦 𝒦') : Set M := by
  classical
  exact 𝒦'.map '' (boundaryComplex 2 (splittingDisk 𝒦'.complex e.1 e.2.1)).space

theorem isPLCellOn_section34GraphSplitCell [FiniteDimensional ℝ Ea]
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hK : IsCombinatorialManifold 3 𝒦'.complex) (e : Section34EdgeIndex 𝒦 𝒦') :
    IsPLCellOn 2 (section34GraphSplitCell 𝒦 𝒦' e)
      (section34GraphSplitBoundary 𝒦 𝒦' e) :=
  𝒦'.isPLCellOn_splittingDisk hK ⟨e.1, e.2.1, e.2.2.1⟩

theorem locallyFinite_section34GraphSplitCell
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) :
    ∀ x ∈ U, ∃ V ∈ 𝓝 x, {e : Section34EdgeIndex 𝒦 𝒦' |
      (section34GraphSplitCell 𝒦 𝒦' e ∩ V).Nonempty}.Finite := by
  classical
  let f : Section34EdgeIndex 𝒦 𝒦' →
      {s : Finset Ea // s ∈ 𝒦'.complex.faces ∧ s.card = 2} :=
    fun e => ⟨e.1, e.2.1, e.2.2.1⟩
  have hf : Function.Injective f := by
    intro e d h
    exact Subtype.ext (congrArg
      (fun s : {s : Finset Ea // s ∈ 𝒦'.complex.faces ∧ s.card = 2} => s.1) h)
  intro x hx
  obtain ⟨V, hV, hfin⟩ := 𝒦'.locallyFinite_image_splittingDisk x hx
  exact ⟨V, hV, hfin.preimage (f := f) hf.injOn⟩

theorem pairwise_disjoint_section34GraphSplitCell
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) :
    Pairwise (Disjoint on section34GraphSplitCell 𝒦 𝒦') := by
  intro e f hef
  apply 𝒦'.pairwise_disjoint_image_splittingDisk
    (i := ⟨e.1, e.2.1, e.2.2.1⟩) (j := ⟨f.1, f.2.1, f.2.2.1⟩)
  exact fun h => hef (Subtype.ext (congrArg
    (fun s : {s : Finset Ea // s ∈ 𝒦'.complex.faces ∧ s.card = 2} => s.1) h))

theorem section34GraphSplitCell_inter_simplexBody_nonempty_iff
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (e : Section34EdgeIndex 𝒦 𝒦') {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    (section34GraphSplitCell 𝒦 𝒦' e ∩ simplexBody 𝒦 t).Nonempty ↔
      Section34Incident e.1 t := by
  classical
  constructor
  · rintro ⟨y, ⟨a, ha, hay⟩, b, hb, hby⟩
    have haK := (splittingDisk_space_subset 𝒦'.complex e.2.1 ha)
    have hab : a = b := 𝒦.bijOn.injOn (hsub.space_eq.subset haK)
      (𝒦.complex.convexHull_subset_space ht hb)
      (by simpa only [hmap] using hay.trans hby.symm)
    rw [← hab] at hb
    obtain ⟨s, hs, has, hst⟩ := hsub.exists_face_subset_of_mem ht hb
    have hes := subset_of_mem_dualCell_of_mem_convexHull 𝒦'.complex e.2.1 hs
      (splittingDisk_space_subset_dualCell 𝒦'.complex e.2.1 ha) has
    intro z hz
    exact hst (subset_convexHull ℝ _ (hes hz))
  · intro he
    have hcenter := e.1.centroid_mem_convexHull (R := ℝ)
      (𝒦'.complex.nonempty_of_mem_faces e.2.1)
    have hsubhull := convexHull_min he (convex_convexHull ℝ (t : Set Ea))
    refine ⟨𝒦'.map (e.1.centroid ℝ id), mem_image_of_mem _
      (centroid_mem_splittingDisk_space 𝒦'.complex e.2.1),
      e.1.centroid ℝ id, hsubhull hcenter, ?_⟩
    rw [hmap]

theorem vertex_subset_edge_of_section34GraphVertexCell_inter_splitCell_nonempty
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
    (hne : (section34GraphVertexCell 𝒦 𝒦' w ∩ section34GraphSplitCell 𝒦 𝒦' e).Nonempty) :
    w.1 ⊆ e.1 := by
  classical
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  obtain ⟨y, ⟨a, ha, hay⟩, b, hb, hby⟩ := hne
  have haK := derivedNeighborhood_space_subset 𝒦'.complex L
    (graphDualCell_space_subset 𝒦'.complex L (w.1.centroid ℝ id) ha)
  have hbK := splittingDisk_space_subset 𝒦'.complex e.2.1 hb
  have hab := 𝒦'.bijOn.injOn haK hbK (hay.trans hby.symm)
  have hcore := isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap
  have hcard : ∀ s ∈ L.faces, s.card ≤ 2 := fun s hs => hcore.card_le
    (fun t ht => ((mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp ht).2) hs
  have hv := vertex_mem_of_graphDualCell_inter_splittingDisk_nonempty 𝒦'.complex L
    (restrict_faces_subset _ _) hcard (singleton_centroid_mem_section34GraphCore w)
    e.2.1 e.2.2.1 ⟨a, ha, hab.symm ▸ hb⟩
  rw [section34VertexIndex_eq_singleton_centroid w]
  exact Finset.singleton_subset_iff.mpr hv

theorem exists_section34GraphSplitCell_endpoints
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ w w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' ∧
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ∧
      section34GraphSplitCell 𝒦 𝒦' e =
        section34GraphVertexCell 𝒦 𝒦' w ∩ section34GraphVertexCell 𝒦 𝒦' w' := by
  classical
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  have heL : e.1 ∈ L.faces := ⟨e.2.1, fun x hx => e.2.2.2 (mem_image_of_mem _ hx)⟩
  obtain ⟨v, z, hvz, he⟩ := Finset.card_eq_two.mp e.2.2.1
  have hv : {v} ∈ L.faces := L.down_closed heL (by simp [he]) (Finset.singleton_nonempty v)
  have hz : {z} ∈ L.faces := L.down_closed heL (by simp [he]) (Finset.singleton_nonempty z)
  let w : Section34VertexIndex 𝒦 𝒦' :=
    ⟨{v}, hv.1, by simp, by rintro _ ⟨x, hx, rfl⟩; exact hv.2 hx⟩
  let w' : Section34VertexIndex 𝒦 𝒦' :=
    ⟨{z}, hz.1, by simp, by rintro _ ⟨x, hx, rfl⟩; exact hz.2 hx⟩
  have hcore := isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap
  have hcard : ∀ s ∈ L.faces, s.card ≤ 2 := fun s hs => hcore.card_le
    (fun t ht => ((mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp ht).2) hs
  refine ⟨w, w', ?_, ?_, ?_⟩
  · intro h
    have h' := congrArg Subtype.val h
    exact hvz (Finset.singleton_injective h')
  · simp only [he, w, w', Finset.coe_pair, Finset.coe_singleton, singleton_union]
  · have hinter := 𝒦'.image_graphDualCell_inter L (restrict_faces_subset _ _) hcard hvz
      (he ▸ heL)
    simpa only [section34GraphVertexCell, section34GraphSplitCell, w, w',
      Finset.centroid_singleton, id_eq, he] using hinter.symm

end DifferentialGeometry.Topology.PiecewiseLinear
