/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphTetrahedronBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphEdgeArcs

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
open Classical in
theorem splittingDisk_inter_subcomplex_residual_eq_geometricLink
    (K S L : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : S.faces ⊆ K.faces) (hL : L.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ L.faces) (hmax : ∀ s ∈ L.faces, s.card ≤ e.card) :
    (splittingDisk K e (hL he)).space ∩ closure (S.space \ (derivedNeighborhood K L).space) =
      (SimplicialComplex.geometricLink (barycentricSubdivision (dualCell K e (hL he)))
        {e.centroid ℝ id}).space ∩ S.space := by
  classical
  let X := barycentricSubdivision (dualCell K e (hL he))
  let c := e.centroid ℝ id
  have hlink : ∀ q, q ∈ (SimplicialComplex.geometricLink X {c}).faces ↔
      q ∈ (splittingDisk K e (hL he)).faces ∧ c ∉ q := by
    intro q
    rw [SimplicialComplex.mem_geometricLink_singleton]
    constructor
    · rintro ⟨hqne, hcq, hq⟩
      exact ⟨⟨X.down_closed hq (Finset.subset_insert c q) hqne, hq⟩, hcq⟩
    · rintro ⟨hq, hcq⟩
      exact ⟨X.nonempty_of_mem_faces hq.1, hcq, hq.2⟩
  have hlocal : S.space \ (derivedNeighborhood K L).space =
      S.space \ (derivedNeighborhood S L).space := by
    rw [← derivedNeighborhood_space_inter_subcomplex K S L hS]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hlocal, closure_space_sdiff_derivedNeighborhood_space hS hL]
  apply Subset.antisymm
  · rintro x ⟨hxD, hxR⟩
    obtain ⟨u, ⟨hu, huL⟩, hxu⟩ := mem_iUnion₂.mp hxR
    obtain ⟨q, hq, hxq⟩ := exists_face_mem_openSimplex (splittingDisk K e (hL he)) hxD
    have hxS : x ∈ S.space := derivedNeighborhoodCell_space_subset S u hxu
    have hxuK : x ∈ (derivedNeighborhoodCell K u).space :=
      ((derivedNeighborhoodCell_inter_subcomplex K S hS hu).symm.subset hxu).1
    have hqK := splittingDisk_faces_subset K (hL he) hq
    have hqu := mem_faces_of_mem_openSimplex_of_mem_space
      (derivedNeighborhoodCell_faces_subset K u) hqK hxq hxuK
    refine ⟨?_, hxS⟩
    apply (SimplicialComplex.geometricLink X {c}).convexHull_subset_space
      ((hlink q).mpr ⟨hq, ?_⟩) (openSimplex_subset_convexHull q hxq)
    intro hcq
    obtain ⟨D, hD, hDne, rfl⟩ := hqK
    have huc := (mem_derivedNeighborhoodCell_faces_iff_of_flag (hS hu) hD hDne).mp hqu
    obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp hcq
    have hde : d = {c} := injOn_faces_of_mem_openSimplex _
      (centroid_mem_openSimplex_of_mem_faces _) (hD.mem_faces hd)
      (singleton_centroid_mem_barycentricSubdivision K (hL he))
      (by simpa only [Finset.centroid_singleton, id_eq, c] using hdc)
    have huc' : u.centroid ℝ id = e.centroid ℝ id := by
      simpa only [hde, Finset.mem_singleton, c] using huc d hd
    exact huL ((injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) (hS hu) (hL he) huc').symm ▸ he)
  · rintro x ⟨hx, hxS⟩
    obtain ⟨q, hq, hxq⟩ := (SimplicialComplex.geometricLink X {c}).mem_space_iff.mp hx
    obtain ⟨hqD, hcq⟩ := (hlink q).mp hq
    refine ⟨(splittingDisk K e (hL he)).convexHull_subset_space hqD hxq, ?_⟩
    obtain ⟨D, hD, hDne, rfl⟩ := splittingDisk_faces_subset K (hL he) hqD
    obtain ⟨hdual, hcenter⟩ := (mem_splittingDisk_faces_iff_of_flag (hL he) hD hDne).mp hqD
    obtain ⟨d, hd, hbot⟩ := hD.exists_bot hDne
    have hcd : c ∈ d := hcenter d hd
    have hdne : d ≠ {c} := by
      intro hde
      apply hcq
      exact Finset.mem_image.mpr ⟨d, hd, by simp only [hde, Finset.centroid_singleton, id_eq]⟩
    obtain ⟨y, hyd, hyc⟩ : ∃ y ∈ d, y ≠ c := by
      by_contra h
      push Not at h
      exact hdne (Finset.eq_singleton_iff_unique_mem.mpr ⟨hcd, h⟩)
    obtain ⟨F, hF, hFne, heF, hdF⟩ := (mem_dualCell_faces_iff K (hL he)).mp (hdual d hd)
    obtain ⟨u, huF, huy⟩ := Finset.mem_image.mp (hdF ▸ hyd)
    have hu : u ∈ K.faces := hF.mem_faces huF
    have heu : e ⊆ u := heF u huF
    have hue : u ≠ e := by
      intro hue
      exact hyc (huy.symm.trans (congrArg (fun z : Finset E => z.centroid ℝ id) hue))
    have huL : u ∉ L.faces := by
      intro huL
      exact hue (Finset.eq_of_subset_of_card_le heu (hmax u huL)).symm
    have huc : ∀ f ∈ D, u.centroid ℝ id ∈ f := by
      intro f hf
      exact hbot f hf (huy.symm ▸ hyd)
    have hxu : x ∈ (derivedNeighborhoodCell K u).space :=
      (derivedNeighborhoodCell K u).convexHull_subset_space
        ((mem_derivedNeighborhoodCell_faces_iff_of_flag hu hD hDne).mpr huc) hxq
    have huS := mem_faces_of_derivedNeighborhoodCell_inter_subcomplex_nonempty K S hS hu
      ⟨x, hxu, hxS⟩
    exact mem_iUnion₂.mpr ⟨u, ⟨huS, huL⟩,
      (derivedNeighborhoodCell_inter_subcomplex K S hS huS).subset ⟨hxu, hxS⟩⟩

open Classical in
theorem LocallyFinitePLPieceIn.boundaryComplex_splittingDisk_eq_geometricLink
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {U : Set M} (T : LocallyFinitePLPieceIn E 3 M U)
    (hK : IsCombinatorialManifold 3 T.complex)
    (e : {s : Finset E // s ∈ T.complex.faces ∧ s.card = 2}) :
    boundaryComplex 2 (splittingDisk T.complex e.1 e.2.1) =
      SimplicialComplex.geometricLink (barycentricSubdivision (dualCell T.complex e.1 e.2.1))
        {e.1.centroid ℝ id} := by
  classical
  let _ : Finite (dualCell T.complex e.1 e.2.1).faces :=
    (T.dualCell_faces_finite e.2.1).to_subtype
  have hupper : (upperLink T.complex e.1).faces.Finite := by
    rw [← geometricLink_dualCell T.complex e.2.1]
    exact (T.dualCell_faces_finite e.2.1).subset (SimplicialComplex.geometricLink_le _ _)
  let _ : Finite (upperLink T.complex e.1).faces := hupper.to_subtype
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_upperLink_of_faces_finite T.complex e.2.1 hupper
  have hupperSphere : IsPLSphere 1 (upperLink T.complex e.1).space :=
    (T.isPLSphere_geometricLink hK e.2.1 (k := 1) e.2.2 (by omega)).of_isPLHomeomorphOn hf.symm
  let X := barycentricSubdivision (dualCell T.complex e.1 e.2.1)
  let c := e.1.centroid ℝ id
  have hc : {c} ∈ X.faces :=
    (barycentricSubdivision_isSubdivision _).singleton_mem
      (singleton_centroid_mem_dualCell T.complex e.2.1)
  have hball : IsPLBall 2 X.space := by
    rw [show X.space = (dualCell T.complex e.1 e.2.1).space from
      (barycentricSubdivision_isSubdivision _).space_eq]
    exact (isConeBase_upperLink T.complex e.2.1).isPLBall_of_isPLSphere hupperSphere
  have hlink : IsPLSphere 1 (SimplicialComplex.geometricLink X {c}).space := by
    rw [isPLSphere_geometricLink_iff_of_isSubdivision (barycentricSubdivision_isSubdivision _)
      (singleton_centroid_mem_dualCell T.complex e.2.1), geometricLink_dualCell]
    exact hupperSphere
  ext q
  change q ∈ (boundaryComplex (1 + 1) (starComplex X c)).faces ↔
    q ∈ (SimplicialComplex.geometricLink X {c}).faces
  rw [hball.isCombinatorialManifoldWithBoundary.mem_boundaryComplex_starComplex_faces_iff
    hc hlink, SimplicialComplex.mem_geometricLink_singleton]
  exact ⟨fun h => ⟨X.nonempty_of_mem_faces h.1.1, h.2, h.1.2⟩,
    fun h => ⟨⟨X.down_closed h.2.2 (Finset.subset_insert c q) h.1, h.2.2⟩, h.2.1⟩⟩

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem section34GraphSplitCell_inter_residual_eq_boundary_inter_simplexBody
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (e : Section34EdgeIndex 𝒦 𝒦')
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    section34GraphSplitCell 𝒦 𝒦' e ∩ section34GraphResidualCell 𝒦 𝒦' t =
      section34GraphSplitBoundary 𝒦 𝒦' e ∩ simplexBody 𝒦 t := by
  classical
  let S := restrict 𝒦'.complex (convexHull ℝ (t : Set Ea))
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  have hSspace : S.space = convexHull ℝ (t : Set Ea) :=
    restrict_space_of_eq_biUnion 𝒦'.complex _ (hsub.convexHull_eq_biUnion ht)
  have hS : S.faces ⊆ 𝒦'.complex.faces := restrict_faces_subset _ _
  have hL : L.faces ⊆ 𝒦'.complex.faces := restrict_faces_subset _ _
  have he : e.1 ∈ L.faces := ⟨e.2.1, fun x hx => e.2.2.2 (mem_image_of_mem _ hx)⟩
  have hcore := isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap
  have hmax : ∀ s ∈ L.faces, s.card ≤ e.1.card := by
    intro s hs
    rw [e.2.2.1]
    exact hcore.card_le
      (fun q hq => ((mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp hq).2) hs
  let _ : Finite S.faces := (𝒦'.restrict_faces_finite_of_isCompact
    (t.finite_toSet.isCompact_convexHull ℝ)
      ((𝒦.complex.convexHull_subset_space ht).trans hsub.space_eq.symm.subset)).to_subtype
  have hraw := splittingDisk_inter_subcomplex_residual_eq_geometricLink
    𝒦'.complex S L hS hL he hmax
  rw [← 𝒦'.boundaryComplex_splittingDisk_eq_geometricLink hK'
    ⟨e.1, e.2.1, e.2.2.1⟩, hSspace] at hraw
  have hbody : convexHull ℝ (t : Set Ea) ⊆ 𝒦'.complex.space :=
    (𝒦.complex.convexHull_subset_space ht).trans hsub.space_eq.symm.subset
  have hcl : closure (convexHull ℝ (t : Set Ea) \ (derivedNeighborhood 𝒦'.complex L).space) ⊆
      𝒦'.complex.space :=
    (closure_minimal sdiff_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed).trans hbody
  have hD := splittingDisk_space_subset 𝒦'.complex e.2.1
  have hB := (space_mono_of_faces_subset
    (boundaryComplex_faces_subset 2 (splittingDisk 𝒦'.complex e.1 e.2.1))).trans hD
  change (𝒦'.map '' (splittingDisk 𝒦'.complex e.1 e.2.1).space) ∩ _ =
    (𝒦'.map '' (boundaryComplex 2 (splittingDisk 𝒦'.complex e.1 e.2.1)).space) ∩ _
  rw [← image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap ht,
    show simplexBody 𝒦 t = 𝒦'.map '' convexHull ℝ (t : Set Ea) by rw [hmap]; rfl,
    ← 𝒦'.bijOn.injOn.image_inter hD hcl, ← 𝒦'.bijOn.injOn.image_inter hB hbody, hraw]

theorem section34GraphSplitBoundary_eq_iUnion_edgeArcs
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (e : Section34EdgeIndex 𝒦 𝒦') :
    section34GraphSplitBoundary 𝒦 𝒦' e =
      ⋃ t : Section34SimplexIndex 𝒦 4, ⋃ (_ : Section34Incident e.1 t.1),
        section34GraphResidualCell 𝒦 𝒦' t.1 ∩ section34GraphSplitCell 𝒦 𝒦' e := by
  apply Subset.antisymm
  · intro x hx
    have hxE := (isPLCellOn_section34GraphSplitCell hK' e).boundary_subset hx
    obtain ⟨z, hz, hzx⟩ := hxE
    have hzK := hsub.space_eq ▸ splittingDisk_space_subset 𝒦'.complex e.2.1 hz
    obtain ⟨s, hs, hzs⟩ := 𝒦.complex.mem_space_iff.mp hzK
    obtain ⟨t, ht, hst, hcard⟩ := 𝒦.exists_face_superset_card_eq hK hs
    let ti : Section34SimplexIndex 𝒦 4 := ⟨t, ht, hcard⟩
    have hxt : x ∈ simplexBody 𝒦 t :=
      ⟨z, convexHull_mono (Finset.coe_subset.mpr hst) hzs, hmap ▸ hzx⟩
    have hxE' : x ∈ section34GraphSplitCell 𝒦 𝒦' e := ⟨z, hz, hzx⟩
    have het := (section34GraphSplitCell_inter_simplexBody_nonempty_iff
      hsub hmap e ht).mp ⟨x, hxE', hxt⟩
    have hxR := ((section34GraphSplitCell_inter_residual_eq_boundary_inter_simplexBody
      hsub hmap hK' e ht).symm.subset ⟨hx, hxt⟩).2
    exact mem_iUnion₂.mpr ⟨ti, het, hxR, hxE'⟩
  · refine iUnion₂_subset fun t _ => ?_
    intro x hx
    exact ((section34GraphSplitCell_inter_residual_eq_boundary_inter_simplexBody
      hsub hmap hK' e t.2.1).subset ⟨hx.2, hx.1⟩).1

theorem section34GraphSplitBoundary_eq_iUnion_proper_faces
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (e : Section34EdgeIndex 𝒦 𝒦') :
    section34GraphSplitBoundary 𝒦 𝒦' e =
      ⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.splitDisk e) \ {.splitDisk e},
        section34GraphCutFamily 𝒦 𝒦' m := by
  classical
  have hE := isPLCellOn_section34GraphSplitCell hK' e
  apply Subset.antisymm
  · intro x hx
    rw [section34GraphSplitBoundary_eq_iUnion_edgeArcs hsub hmap hK hK'] at hx
    obtain ⟨t, het, hxt⟩ := mem_iUnion₂.mp hx
    let i : Section34EdgeArcIndex 𝒦 𝒦' := ⟨(t, e), het⟩
    exact mem_iUnion₂.mpr ⟨.edgeArc i, ⟨inter_subset_right, by simp⟩, hxt⟩
  · refine iUnion₂_subset fun l hl => ?_
    have hsubE : section34GraphCutFamily 𝒦 𝒦' l ⊆ section34GraphSplitCell 𝒦 𝒦' e := hl.1
    have hR : ∀ t, t ∈ 𝒦.complex.faces → ∀ x,
        x ∈ section34GraphResidualCell 𝒦 𝒦' t → x ∈ section34GraphSplitCell 𝒦 𝒦' e →
        x ∈ section34GraphSplitBoundary 𝒦 𝒦' e := fun t ht x hxR hxE =>
      ((section34GraphSplitCell_inter_residual_eq_boundary_inter_simplexBody
        hsub hmap hK' e ht).subset ⟨hxE, hxR⟩).1
    cases l with
    | vertexBall w =>
        exact ((isPLCellOn_section34GraphVertexCell hsub hmap
          hK'.isCombinatorialManifoldWithBoundary w).not_subset_of_lower_dimension
            hE (by omega) hsubE).elim
    | tetraBall t =>
        obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphResidualTetrahedron hsub hmap t
        exact (hB.not_subset_of_lower_dimension hE (by omega) hsubE).elim
    | splitDisk d =>
        exact (hl.2 (congrArg Section34Label.splitDisk
          ((section34GraphSplitCell_subset_iff d e).mp hsubE))).elim
    | faceDisk s => exact fun x hx => hR s.1 s.2.1 x hx (hsubE hx)
    | patch p => exact fun x hx => hR p.1.1.1 p.1.1.2.1 x hx.1 (hsubE hx)
    | faceArc a => exact fun x hx => hR a.1.1.1 a.1.1.2.1 x hx.2 (hsubE hx)
    | edgeArc i => exact fun x hx => hR i.1.1.1 i.1.1.2.1 x hx.1 (hsubE hx)
    | markedPoint p => exact fun x hx => hR p.1.1.1 p.1.1.2.1 x hx.2 (hsubE hx)

theorem isPLCellOn_section34GraphSplitCell_proper_faces
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (e : Section34EdgeIndex 𝒦 𝒦') :
    IsPLCellOn 2 (section34GraphSplitCell 𝒦 𝒦' e)
      (⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.splitDisk e) \ {.splitDisk e},
        section34GraphCutFamily 𝒦 𝒦' m) := by
  rw [← section34GraphSplitBoundary_eq_iUnion_proper_faces hsub hmap hK hK']
  exact isPLCellOn_section34GraphSplitCell hK' e

end DifferentialGeometry.Topology.PiecewiseLinear
