/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RefinedResidualCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualCover

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem mem_faces_of_derivedNeighborhoodCell_inter_subcomplex_nonempty
    (K S : Geometry.SimplicialComplex ℝ E) (hSK : S.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces)
    (hne : ((derivedNeighborhoodCell K s).space ∩ S.space).Nonempty) : s ∈ S.faces := by
  obtain ⟨x, hxC, hxS⟩ := hne
  have hxS' : x ∈ (barycentricSubdivision S).space :=
    (barycentricSubdivision_isSubdivision S).space_eq.symm ▸ hxS
  obtain ⟨t, ht, hxt⟩ := (barycentricSubdivision S).mem_space_iff.mp hxS'
  rw [derivedNeighborhoodCell_eq_dualCell K hs] at hxC
  have hst := subset_of_mem_dualCell_of_mem_convexHull (barycentricSubdivision K)
    (singleton_centroid_mem_barycentricSubdivision K hs)
    (barycentricSubdivision_faces_subset hSK ht) hxC hxt
  have hcent : s.centroid ℝ id ∈ S.space :=
    (barycentricSubdivision_isSubdivision S).space_eq ▸
      (barycentricSubdivision S).convexHull_subset_space ht
        (subset_convexHull ℝ _ (hst (Finset.mem_singleton_self _)))
  exact mem_faces_of_mem_openSimplex_of_mem_space hSK hs
    (centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)) hcent

open Classical in
theorem closure_sdiff_derivedNeighborhood_inter_subcomplex_ambient
    (A K S L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hKA : K.faces ⊆ A.faces) (hSK : S.faces ⊆ K.faces) (hLA : L.faces ⊆ A.faces) :
    closure (K.space \ (derivedNeighborhood A L).space) ∩ S.space =
      closure (S.space \ (derivedNeighborhood A L).space) := by
  let _ : Finite S.faces := ((Set.toFinite K.faces).subset hSK).to_subtype
  have hlocal (R : Geometry.SimplicialComplex ℝ E) (hRA : R.faces ⊆ A.faces) :
      R.space \ (derivedNeighborhood A L).space =
        R.space \ (derivedNeighborhood R L).space := by
    rw [← derivedNeighborhood_space_inter_subcomplex A R L hRA]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hlocal K hKA, hlocal S (hSK.trans hKA),
    closure_space_sdiff_derivedNeighborhood_space hKA hLA,
    closure_space_sdiff_derivedNeighborhood_space (hSK.trans hKA) hLA]
  apply Subset.antisymm
  · rintro x ⟨hxK, hxS⟩
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hxK
    have hsS := mem_faces_of_derivedNeighborhoodCell_inter_subcomplex_nonempty K S hSK hs.1
      ⟨x, hxs, hxS⟩
    exact mem_iUnion₂.mpr ⟨s, ⟨hsS, hs.2⟩,
      (derivedNeighborhoodCell_inter_subcomplex K S hSK hsS).subset ⟨hxs, hxS⟩⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    have htrace := (derivedNeighborhoodCell_inter_subcomplex K S hSK hs.1).symm.subset hxs
    exact ⟨mem_iUnion₂.mpr ⟨s, ⟨hSK hs.1, hs.2⟩, htrace.1⟩, htrace.2⟩

variable {M : Type*} [TopologicalSpace M] {d : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] {U : Set M}

open Classical in
theorem LocallyFinitePLPieceIn.closure_residual_inter_coarse_face
    (T : LocallyFinitePLPieceIn E d M U) {K L : Geometry.SimplicialComplex ℝ E}
    (hsub : IsSubdivision T.complex K) (hL : L.faces ⊆ T.complex.faces)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ⊆ t) :
    closure (convexHull ℝ (t : Set E) \ (derivedNeighborhood T.complex L).space) ∩
        convexHull ℝ (s : Set E) =
      closure (convexHull ℝ (s : Set E) \ (derivedNeighborhood T.complex L).space) := by
  let A := DifferentialGeometry.Topology.PiecewiseLinear.restrict
    T.complex (convexHull ℝ (t : Set E))
  let S := DifferentialGeometry.Topology.PiecewiseLinear.restrict
    T.complex (convexHull ℝ (s : Set E))
  have hAt : A.space = convexHull ℝ (t : Set E) :=
    restrict_space_of_eq_biUnion T.complex _ (hsub.convexHull_eq_biUnion ht)
  have hSs : S.space = convexHull ℝ (s : Set E) :=
    restrict_space_of_eq_biUnion T.complex _ (hsub.convexHull_eq_biUnion hs)
  have hSA : S.faces ⊆ A.faces := fun u hu =>
    ⟨hu.1, hu.2.trans (convexHull_mono (Finset.coe_subset.mpr hst))⟩
  let _ : Finite A.faces := (T.restrict_faces_finite_of_isCompact
    (t.finite_toSet.isCompact_convexHull ℝ)
      ((K.convexHull_subset_space ht).trans hsub.space_eq.symm.subset)).to_subtype
  have h := closure_sdiff_derivedNeighborhood_inter_subcomplex_ambient T.complex A S L
    (restrict_faces_subset _ _) hSA hL
  simpa only [hAt, hSs] using h

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M3 : Type*} [TopologicalSpace M3] [T2Space M3]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M3] {V : Set M3}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M3 V}

open Classical in
theorem section34GraphResidualCell_inter_simplexBody
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    {s t : Finset Ea} (hs : s ∈ 𝒦.complex.faces) (ht : t ∈ 𝒦.complex.faces) (hst : s ⊆ t) :
    section34GraphResidualCell 𝒦 𝒦' t ∩ simplexBody 𝒦 s =
      section34GraphResidualCell 𝒦 𝒦' s := by
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  have hcl : closure (convexHull ℝ (t : Set Ea) \ (derivedNeighborhood 𝒦'.complex L).space) ⊆
      𝒦'.complex.space :=
    (closure_minimal sdiff_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed).trans
      ((𝒦.complex.convexHull_subset_space ht).trans hsub.space_eq.symm.subset)
  have hHs : convexHull ℝ (s : Set Ea) ⊆ 𝒦'.complex.space :=
    (𝒦.complex.convexHull_subset_space hs).trans hsub.space_eq.symm.subset
  have hbody : simplexBody 𝒦 s = 𝒦'.map '' convexHull ℝ (s : Set Ea) := by
    rw [hmap]
    rfl
  rw [← image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap ht,
    ← image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap hs, hbody,
    ← 𝒦'.bijOn.injOn.image_inter hcl hHs,
    𝒦'.closure_residual_inter_coarse_face hsub (restrict_faces_subset _ _) hs ht hst]

open Classical in
theorem section34GraphResidualCell_inter
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    {s t : Finset Ea} (hs : s ∈ 𝒦.complex.faces) (ht : t ∈ 𝒦.complex.faces) :
    section34GraphResidualCell 𝒦 𝒦' s ∩ section34GraphResidualCell 𝒦 𝒦' t =
      section34GraphResidualCell 𝒦 𝒦' (s ∩ t) := by
  have hbody : simplexBody 𝒦 (s ∩ t) = simplexBody 𝒦 s ∩ simplexBody 𝒦 t := by
    simp only [simplexBody, Finset.coe_inter]
    rw [← 𝒦.complex.convexHull_inter_convexHull hs ht]
    exact 𝒦.bijOn.injOn.image_inter (𝒦.complex.convexHull_subset_space hs)
      (𝒦.complex.convexHull_subset_space ht)
  rcases (s ∩ t).eq_empty_or_nonempty with hem | hne
  · have hR : section34GraphResidualCell 𝒦 𝒦' ∅ = ∅ := by
      simp [section34GraphResidualCell, simplexBody]
    have hB : simplexBody 𝒦 s ∩ simplexBody 𝒦 t = ∅ := by
      rw [← hbody, hem]
      simp [simplexBody]
    rw [hem, hR]
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxS, hxT⟩
    have hx : x ∈ simplexBody 𝒦 s ∩ simplexBody 𝒦 t :=
      ⟨section34GraphResidualCell_subset_simplexBody hs hxS,
        section34GraphResidualCell_subset_simplexBody ht hxT⟩
    simp only [hB, mem_empty_iff_false] at hx
  · have hi := 𝒦.complex.down_closed hs Finset.inter_subset_left hne
    have htraceS := section34GraphResidualCell_inter_simplexBody hsub hmap hi hs
      Finset.inter_subset_left
    have htraceT := section34GraphResidualCell_inter_simplexBody hsub hmap hi ht
      Finset.inter_subset_right
    apply Subset.antisymm
    · rintro x ⟨hxS, hxT⟩
      exact htraceS.subset ⟨hxS, hbody.symm.subset
        ⟨section34GraphResidualCell_subset_simplexBody hs hxS,
          section34GraphResidualCell_subset_simplexBody ht hxT⟩⟩
    · intro x hx
      exact ⟨(htraceS.symm.subset hx).1, (htraceT.symm.subset hx).1⟩

omit [T2Space M3] in
theorem section34GraphResidualCell_eq_empty_of_card_le_two
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) (hcard : t.card ≤ 2) :
    section34GraphResidualCell 𝒦 𝒦' t = ∅ := by
  classical
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  have hLN : L.space ⊆ (derivedNeighborhood 𝒦'.complex L).space := by
    rw [← iUnion_derivedNeighborhoodCell_space 𝒦'.complex L (restrict_faces_subset _ _)]
    exact space_subset_iUnion_derivedNeighborhoodCell_space _ _ (restrict_faces_subset _ _)
  have hcore : 𝒦'.map '' L.space = graphSkeletonSpace 𝒦 := by
    rw [(isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap).space_eq, hmap,
      image_restrict_preimage_graphSkeletonSpace]
  have hbody : simplexBody 𝒦 t ⊆ graphSkeletonSpace 𝒦 :=
    fun x hx => mem_iUnion₂.mpr ⟨t, ⟨ht, hcard⟩, hx⟩
  have hN : graphSkeletonSpace 𝒦 ⊆
      ⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w := by
    calc
      graphSkeletonSpace 𝒦 = 𝒦'.map '' L.space := hcore.symm
      _ ⊆ 𝒦'.map '' (derivedNeighborhood 𝒦'.complex L).space := image_mono hLN
      _ = ⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w :=
        (iUnion_section34GraphVertexCell 𝒦 𝒦').symm
  rw [section34GraphResidualCell, sdiff_eq_empty.mpr (hbody.trans hN), closure_empty]

theorem pairwiseDisjoint_section34GraphResidualTriangle
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map) :
    Pairwise fun s t : Section34SimplexIndex 𝒦 3 =>
      Disjoint (section34GraphResidualCell 𝒦 𝒦' s.1)
        (section34GraphResidualCell 𝒦 𝒦' t.1) := by
  classical
  intro s t hst
  apply disjoint_iff_inter_eq_empty.mpr
  rw [section34GraphResidualCell_inter hsub hmap s.2.1 t.2.1]
  rcases (s.1 ∩ t.1).eq_empty_or_nonempty with hem | hne
  · simp [hem, section34GraphResidualCell, simplexBody]
  · apply section34GraphResidualCell_eq_empty_of_card_le_two hsub hmap
      (𝒦.complex.down_closed s.2.1 Finset.inter_subset_left hne)
    by_contra hcard
    have h3 : (s.1 ∩ t.1).card = 3 :=
      le_antisymm ((Finset.card_le_card Finset.inter_subset_left).trans s.2.2.le) (by omega)
    have e1 : s.1 ∩ t.1 = s.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h3, s.2.2])
    have e2 : s.1 ∩ t.1 = t.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h3, t.2.2])
    exact hst (Subtype.ext (e1.symm.trans e2))

end DifferentialGeometry.Topology.PiecewiseLinear
