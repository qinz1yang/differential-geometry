/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphPatches
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplementCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualSeparation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_graphDualCell_residual_boundary
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hL : L.faces ⊆ (boundaryComplex 3 K).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    ∃ P : Geometry.SimplicialComplex ℝ E, P.faces.Finite ∧ IsPLBall 2 P.space ∧
      P.space = (graphDualCell K L v).space ∩
        closure (K.space \ (derivedNeighborhood K L).space) ∧
      (boundaryComplex 2 P).space = P.space ∩ ((boundaryComplex 3 K).space ∪
        ⋃ e : {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e},
          (splittingDisk K e.1 (boundaryComplex_faces_subset 3 K (hL e.2.1))).space) := by
  classical
  let C := graphDualCell K L v
  let S := boundaryComplex 3 C
  let I := {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}
  let D := C.space ∩ (boundaryComplex 3 K).space ∪
    ⋃ e : I, (splittingDisk K e.1 (boundaryComplex_faces_subset 3 K (hL e.2.1))).space
  let _ : Finite C.faces := (graphDualCell_faces_finite K L v).to_subtype
  let _ : Finite S.faces := (boundaryComplex_faces_finite 3 C).to_subtype
  have hIfin : {e : Finset E | e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}.Finite :=
    (Set.toFinite K.faces).subset fun _ he => boundaryComplex_faces_subset 3 K (hL he.1)
  let _ : Finite I := hIfin.to_subtype
  let _ : Fintype I := Fintype.ofFinite I
  have hLK := hL.trans (boundaryComplex_faces_subset 3 K)
  have hC : IsPLBall 3 C.space := hK.isPLBall_graphDualCell K L hLK hcard hv
  have hS : IsCombinatorialManifold 2 S :=
    isCombinatorialManifold_boundaryComplex C hC.isCombinatorialManifoldWithBoundary
  have hD : IsPLBall 2 D := by
    simpa only [Finset.mem_univ, iUnion_true] using
      hK.isPLBall_graphDualCell_boundary_contact K L hL hcard hv (Finset.univ : Finset I)
  have hDS : D ⊆ S.space := union_subset
    (inter_boundaryComplex_space_subset_of_subset K C hK
      hC.isCombinatorialManifoldWithBoundary
      ((graphDualCell_space_subset K L v).trans (derivedNeighborhood_space_subset K L)))
    (iUnion_subset fun e => hK.splittingDisk_subset_boundary_graphDualCell K L hLK hcard
      e.2.1 e.2.2.1 e.2.2.2)
  obtain ⟨A, hAfin, hAspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hA : IsPLBall 2 A.space := hAspace.symm ▸ hD
  have hpatch := hK.isPLBall_graphDualCell_inter_residual K L hL hcard hv
  obtain ⟨P, hPfin, hPspace⟩ := hpatch.isPolyhedron.exists_simplicialComplex
  let _ : Finite P.faces := hPfin.to_subtype
  have hP : IsPLBall 2 P.space := hPspace.symm ▸ hpatch
  have hPfree : P.space = closure (S.space \ A.space) := by
    rw [hPspace, graphDualCell_inter_residual_eq_free_boundary K L hK hL hcard hv, hAspace]
  have hSbd : (boundaryComplex 2 S).space = ∅ := by
    rw [Geometry.SimplicialComplex.space, hS.boundaryComplex_faces_eq_empty S]
    simp
  have hbd := boundaryComplex_space_of_closure_sdiff_of_boundary_subset S A P
    hS.isCombinatorialManifoldWithBoundary hA.isCombinatorialManifoldWithBoundary
    (hAspace.symm ▸ hDS) hP.isCombinatorialManifoldWithBoundary hPfree
    (by rw [hSbd]; exact empty_subset _)
  refine ⟨P, hPfin, hP, hPspace, ?_⟩
  rw [hbd, hAspace]
  ext x
  constructor
  · rintro ⟨hxP, hxD⟩
    exact ⟨hxP, hxD.imp And.right id⟩
  · rintro ⟨hxP, hxD⟩
    exact ⟨hxP, hxD.imp (fun hxB => ⟨(hPspace.subset hxP).1, hxB⟩) id⟩

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem exists_isPLCellOn_section34GraphPatch_boundary
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦')
    (hwt : Section34Incident w.1 t.1) :
    ∃ B, IsPLCellOn 2 (section34GraphVertexCell 𝒦 𝒦' w ∩
        section34GraphResidualCell 𝒦 𝒦' t.1) B ∧
      B = (section34GraphVertexCell 𝒦 𝒦' w ∩ section34GraphResidualCell 𝒦 𝒦' t.1) ∩
        (simplexRim 𝒦 t.1 ∪ ⋃ e : Section34EdgeIndex 𝒦 𝒦',
          section34GraphSplitCell 𝒦 𝒦' e) := by
  classical
  let S₀ := simplexComplex t.1 (𝒦.complex.indep t.2.1)
  let B₀ := simplexBoundary t.1 (𝒦.complex.indep t.2.1)
  let S := restrict 𝒦'.complex (convexHull ℝ (t.1 : Set Ea))
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  let L₀ := restrict 𝒦.complex (𝒦.map ⁻¹' graphSkeletonSpace 𝒦)
  let G := restrict L S.space
  have hS₀space : S₀.space = convexHull ℝ (t.1 : Set Ea) :=
    simplexComplex_space _ _ (𝒦.complex.nonempty_of_mem_faces t.2.1)
  have hS₀K : S₀.faces ⊆ 𝒦.complex.faces :=
    fun _ ht => 𝒦.complex.down_closed t.2.1 ht.2 ht.1
  have hSsub : IsSubdivision S S₀ := by
    simpa only [hS₀space] using hsub.restrict S₀ hS₀K
  have hSspace : S.space = convexHull ℝ (t.1 : Set Ea) := hSsub.space_eq.trans hS₀space
  have hS₀ : IsPLBall 3 S₀.space := hS₀space.symm ▸
    isPLBall_convexHull_of_affineIndependent t.1 (𝒦.complex.indep t.2.1) t.2.2
  have hS : IsPLBall 3 S.space := hSsub.space_eq.symm ▸ hS₀
  let _ : Finite S₀.faces := (simplexComplex_faces_finite _ _).to_subtype
  let _ : Finite S.faces := (𝒦'.restrict_faces_finite_of_isCompact
    (t.1.finite_toSet.isCompact_convexHull ℝ)
      ((𝒦.complex.convexHull_subset_space t.2.1).trans hsub.space_eq.symm.subset)).to_subtype
  have hSbd : (boundaryComplex 3 S).space = B₀.space := by
    rw [boundaryComplex_space_of_isSubdivision S₀ S hS₀.isCombinatorialManifoldWithBoundary
      hSsub, show boundaryComplex 3 S₀ = B₀ from
        boundaryComplex_simplexComplex (𝒦.complex.indep t.2.1) t.2.2]
  have hcore := isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap
  have hGS : G.faces ⊆ S.faces := fun f hf =>
    ((mem_restrict_faces_iff_of_faces_subset 𝒦'.complex L S
      (restrict_faces_subset _ _) (restrict_faces_subset _ _)).mp hf).2
  have hGB : G.faces ⊆ (boundaryComplex 3 S).faces := by
    intro f hf
    have hfS := hGS hf
    have hcen : f.centroid ℝ id ∈ convexHull ℝ (f : Set Ea) :=
      f.centroid_mem_convexHull (S.nonempty_of_mem_faces hfS)
    have hxL : f.centroid ℝ id ∈ L₀.space := hcore.space_eq ▸
      L.convexHull_subset_space hf.1 hcen
    obtain ⟨q, hq, hxq⟩ := L₀.mem_space_iff.mp hxL
    obtain ⟨hqK, hqcard⟩ := (mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp hq
    have hxqt : f.centroid ℝ id ∈ convexHull ℝ ((q ∩ t.1 : Finset Ea) : Set Ea) := by
      rw [Finset.coe_inter, ← 𝒦.complex.convexHull_inter_convexHull hqK t.2.1]
      exact ⟨hxq, hfS.2 hcen⟩
    have hqne : (q ∩ t.1).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h] at hxqt
      simp only [Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hxqt
    have hqB : q ∩ t.1 ∈ B₀.faces := by
      refine ⟨Finset.inter_subset_right, hqne, ?_⟩
      intro heq
      have hle := Finset.card_le_card (Finset.inter_subset_left : q ∩ t.1 ⊆ q)
      rw [heq, t.2.2] at hle
      omega
    apply mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 S) hfS
      (centroid_mem_openSimplex (S.nonempty_of_mem_faces hfS))
    rw [hSbd]
    exact B₀.convexHull_subset_space hqB hxqt
  have hcard : ∀ f ∈ G.faces, f.card ≤ 2 := fun f hf =>
    hcore.card_le (fun q hq => ((mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp hq).2)
      hf.1
  let v := w.1.centroid ℝ id
  have hvS : {v} ∈ S.faces := by
    rw [show ({v} : Finset Ea) = w.1 from (section34VertexIndex_eq_singleton_centroid w).symm]
    exact ⟨w.2.1, convexHull_min hwt (convex_convexHull ℝ (t.1 : Set Ea))⟩
  have hvG : {v} ∈ G.faces :=
    ⟨singleton_centroid_mem_section34GraphCore w, hSspace.symm ▸ hvS.2⟩
  obtain ⟨P, hPfin, hP, hPspace, hPbd⟩ := exists_graphDualCell_residual_boundary
    S G hS.isCombinatorialManifoldWithBoundary hGB hcard hvG
  let _ : Finite P.faces := hPfin.to_subtype
  have hres : closure (convexHull ℝ (t.1 : Set Ea) \
      (derivedNeighborhood 𝒦'.complex L).space) =
      closure (S.space \ (derivedNeighborhood S G).space) := by
    congr 1
    rw [show G = restrict L S.space from rfl,
      derivedNeighborhood_restrict_core_eq 𝒦'.complex S L
        (restrict_faces_subset _ _) (restrict_faces_subset _ _),
      ← derivedNeighborhood_space_inter_subcomplex 𝒦'.complex S L (restrict_faces_subset _ _),
      hSspace]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  let C := closure (convexHull ℝ (t.1 : Set Ea) \
    (derivedNeighborhood 𝒦'.complex L).space)
  have hCS : C ⊆ S.space := hSspace.symm ▸
    closure_minimal sdiff_subset (t.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hCK : C ⊆ 𝒦'.complex.space :=
    hCS.trans (space_mono_of_faces_subset (restrict_faces_subset _ _))
  have hvertex : (graphDualCell 𝒦'.complex L v).space ⊆ 𝒦'.complex.space :=
    (graphDualCell_space_subset _ _ _).trans (derivedNeighborhood_space_subset _ _)
  have hPraw : P.space = (graphDualCell 𝒦'.complex L v).space ∩ C := by
    rw [← inter_eq_right.mpr hCS, ← inter_assoc,
      graphDualCell_space_inter_subcomplex 𝒦'.complex S L (restrict_faces_subset _ _) hvS]
    have hg : graphDualCell S G v = graphDualCell S L v :=
      graphDualCell_restrict_core_eq 𝒦'.complex S L
        (restrict_faces_subset _ _) (restrict_faces_subset _ _) v
    simpa only [hg, C, hres] using hPspace
  have hPK : P.space ⊆ 𝒦'.complex.space := hPraw.subset.trans (inter_subset_left.trans hvertex)
  have hPS : P.space ⊆ S.space := hPraw.subset.trans (inter_subset_right.trans hCS)
  have himage : 𝒦'.map '' P.space = section34GraphVertexCell 𝒦 𝒦' w ∩
      section34GraphResidualCell 𝒦 𝒦' t.1 := by
    rw [hPraw, 𝒦'.bijOn.injOn.image_inter hvertex hCK,
      image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap t.2.1]
    rfl
  have hB₀K : B₀.space ⊆ 𝒦'.complex.space :=
    (show B₀.space ⊆ convexHull ℝ (t.1 : Set Ea) from fun x hx => by
      obtain ⟨q, hq, hxq⟩ := B₀.mem_space_iff.mp hx
      exact convexHull_mono (Finset.coe_subset.mpr hq.1) hxq).trans
      ((𝒦.complex.convexHull_subset_space t.2.1).trans hsub.space_eq.symm.subset)
  have hrim : 𝒦'.map '' B₀.space = simplexRim 𝒦 t.1 := by
    rw [hmap]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨q, hq, hxq⟩ := B₀.mem_space_iff.mp hx
      exact mem_iUnion₂.mpr ⟨q, Finset.ssubset_iff_subset_ne.mpr ⟨hq.1, hq.2.2⟩,
        x, hxq, rfl⟩
    · intro x hx
      obtain ⟨q, hq, y, hy, rfl⟩ := mem_iUnion₂.mp hx
      have hqne : q.Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hy
        simp only [Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hy
      exact ⟨y, B₀.convexHull_subset_space ⟨hq.subset, hqne, hq.ne⟩ hy, rfl⟩
  have hcell := 𝒦'.isPLCellOn_image_boundaryComplex P hPfin hPK (by omega) hP
  refine ⟨𝒦'.map '' (boundaryComplex 2 P).space, himage ▸ hcell, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyP, hy⟩ := hPbd.subset hy
    refine ⟨himage.subset (mem_image_of_mem _ hyP), ?_⟩
    rcases hy with hyB | hyE
    · exact Or.inl (hrim.subset (mem_image_of_mem _ (hSbd ▸ hyB)))
    · obtain ⟨e, hye⟩ := mem_iUnion.mp hyE
      have heS : e.1 ∈ S.faces := hGS e.2.1
      let e' : Section34EdgeIndex 𝒦 𝒦' := ⟨e.1, heS.1, e.2.2.1, by
        rintro _ ⟨z, hz, rfl⟩
        exact e.2.1.1.2 hz⟩
      refine Or.inr (mem_iUnion.mpr ⟨e', ?_⟩)
      exact mem_image_of_mem _ ((splittingDisk_space_inter_subcomplex 𝒦'.complex S
        (restrict_faces_subset _ _) heS).symm.subset hye).1
  · rintro x ⟨hxP, hx⟩
    obtain ⟨y, hyP, rfl⟩ := himage.symm.subset hxP
    refine mem_image_of_mem _ (hPbd.symm.subset ⟨hyP, ?_⟩)
    rcases hx with hxB | hxE
    · obtain ⟨z, hz, hzy⟩ := hrim.symm.subset hxB
      have hzy' : z = y := 𝒦'.bijOn.injOn (hB₀K hz) (hPK hyP) hzy
      exact Or.inl (hSbd.symm ▸ hzy' ▸ hz)
    · obtain ⟨e, hye⟩ := mem_iUnion.mp hxE
      have het : Section34Incident e.1 t.1 :=
        (section34GraphSplitCell_inter_simplexBody_nonempty_iff hsub hmap e t.2.1).mp
          ⟨_, hye, section34GraphResidualCell_subset_simplexBody t.2.1 hxP.2⟩
      have hwe := vertex_subset_edge_of_section34GraphVertexCell_inter_splitCell_nonempty
        hsub hmap w e ⟨_, hxP.1, hye⟩
      have heS : e.1 ∈ S.faces := ⟨e.2.1,
        convexHull_min het (convex_convexHull ℝ (t.1 : Set Ea))⟩
      have heG : e.1 ∈ G.faces := ⟨⟨e.2.1, fun z hz => e.2.2.2 (mem_image_of_mem _ hz)⟩,
        hSspace.symm ▸ heS.2⟩
      have hve : v ∈ e.1 := hwe (by
        rw [section34VertexIndex_eq_singleton_centroid w]
        exact Finset.mem_singleton_self _)
      obtain ⟨z, hz, hzy⟩ := hye
      have hyE := (𝒦'.bijOn.injOn (splittingDisk_space_subset _ e.2.1 hz)
        (hPK hyP) hzy) ▸ hz
      refine Or.inr (mem_iUnion.mpr ⟨⟨e.1, heG, e.2.2.1, hve⟩, ?_⟩)
      exact (splittingDisk_space_inter_subcomplex 𝒦'.complex S
        (restrict_faces_subset _ _) heS).subset ⟨hyE, hPS hyP⟩

open Classical in
theorem isPLCellOn_section34GraphPatch_proper_faces
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (p : Section34PatchIndex 𝒦 𝒦') :
    IsPLCellOn 2 (section34GraphCutFamily 𝒦 𝒦' (.patch p))
      (⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.patch p) \ {.patch p},
        section34GraphCutFamily 𝒦 𝒦' m) := by
  classical
  let C := section34GraphVertexCell 𝒦 𝒦'
  let R := section34GraphResidualCell 𝒦 𝒦'
  let E := section34GraphSplitCell 𝒦 𝒦'
  obtain ⟨B, hB, hBeq⟩ := exists_isPLCellOn_section34GraphPatch_boundary hsub hmap
    p.1.1 p.1.2 p.2
  have hcell : IsPLCellOn 2 (section34GraphCutFamily 𝒦 𝒦' (.patch p)) B := by
    simpa only [section34GraphCutFamily, inter_comm] using hB
  have htriangle : ∀ s : Section34SimplexIndex 𝒦 3,
      (R s.1 ∩ R p.1.1.1).Nonempty → s.1 ⊆ p.1.1.1 := by
    intro s ⟨x, hx⟩
    have hxI := (section34GraphResidualCell_inter hsub hmap s.2.1 p.1.1.2.1).subset hx
    by_contra hnot
    have hne : s.1 ∩ p.1.1.1 ≠ s.1 := fun heq => hnot (heq ▸ Finset.inter_subset_right)
    have hcard : (s.1 ∩ p.1.1.1).card ≤ 2 := by
      have hlt := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hne⟩)
      omega
    rcases (s.1 ∩ p.1.1.1).eq_empty_or_nonempty with hem | hnon
    · simp [hem, section34GraphResidualCell, simplexBody] at hxI
    · rw [section34GraphResidualCell_eq_empty_of_card_le_two hsub hmap
        (𝒦.complex.down_closed s.2.1 Finset.inter_subset_left hnon) hcard] at hxI
      exact hxI
  have hrim (s : Section34SimplexIndex 𝒦 3) (hst : s.1 ⊆ p.1.1.1) :
      R s.1 ⊆ simplexRim 𝒦 p.1.1.1 := by
    intro x hx
    have hproper : s.1 ⊂ p.1.1.1 := Finset.ssubset_iff_subset_ne.mpr ⟨hst, fun heq => by
      have := congrArg Finset.card heq
      rw [s.2.2, p.1.1.2.2] at this
      omega⟩
    exact mem_iUnion₂.mpr ⟨s.1, hproper,
      section34GraphResidualCell_subset_simplexBody s.2.1 hx⟩
  suffices B = ⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.patch p) \ {.patch p},
      section34GraphCutFamily 𝒦 𝒦' m by rw [← this]; exact hcell
  rw [hBeq]
  apply Subset.antisymm
  · rintro x ⟨⟨hxC, hxR⟩, hx⟩
    rcases hx with hxrim | hxE
    · obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hxrim
      change q ⊂ p.1.1.1 at hq
      have hqne : q.Nonempty := by
        by_contra h
        simp [Finset.not_nonempty_iff_eq_empty.mp h, simplexBody] at hxq
      have hqK := 𝒦.complex.down_closed p.1.1.2.1 hq.subset hqne
      have hxRq : x ∈ R q :=
        (section34GraphResidualCell_inter_simplexBody hsub hmap hqK p.1.1.2.1
          hq.subset).subset ⟨hxR, hxq⟩
      have hqcard : q.card = 3 := by
        have hlt := Finset.card_lt_card hq
        rw [p.1.1.2.2] at hlt
        by_contra h3
        have hsmall : q.card ≤ 2 := by omega
        have hem := section34GraphResidualCell_eq_empty_of_card_le_two hsub hmap hqK hsmall
        exact Set.notMem_empty x (hem ▸ hxRq)
      let s : Section34SimplexIndex 𝒦 3 := ⟨q, hqK, hqcard⟩
      have hws := (section34GraphVertexCell_inter_simplexBody_nonempty_iff
        hsub hmap p.1.2 hqK).mp ⟨x, hxC, hxq⟩
      let a : Section34ArcIndex 𝒦 𝒦' := ⟨(s, p.1.2), hws⟩
      have hsubR : R q ⊆ R p.1.1.1 := section34GraphResidualCell_mono_of_incident
        fun y hy => subset_convexHull ℝ _ (hq.subset hy)
      exact mem_iUnion₂.mpr ⟨.faceArc a,
        ⟨fun y hy => ⟨hsubR hy.2, hy.1⟩, by simp⟩, hxC, hxRq⟩
    · obtain ⟨e, hxe⟩ := mem_iUnion.mp hxE
      have het := (section34GraphSplitCell_inter_simplexBody_nonempty_iff
        hsub hmap e p.1.1.2.1).mp
          ⟨x, hxe, section34GraphResidualCell_subset_simplexBody p.1.1.2.1 hxR⟩
      have hwe := vertex_subset_edge_of_section34GraphVertexCell_inter_splitCell_nonempty
        hsub hmap p.1.2 e ⟨x, hxC, hxe⟩
      have heC := section34GraphSplitCell_subset_vertex_of_subset hsub hmap p.1.2 e hwe
      let a : Section34EdgeArcIndex 𝒦 𝒦' := ⟨(p.1.1, e), het⟩
      exact mem_iUnion₂.mpr ⟨.edgeArc a,
        ⟨fun y hy => ⟨hy.1, heC hy.2⟩, by simp⟩, hxR, hxe⟩
  · refine iUnion₂_subset fun l hl => ?_
    have hsubP : section34GraphCutFamily 𝒦 𝒦' l ⊆
        section34GraphCutFamily 𝒦 𝒦' (.patch p) := hl.1
    have hsubR := hsubP.trans inter_subset_left
    refine subset_inter (fun x hx => ⟨(hsubP hx).2, (hsubP hx).1⟩) ?_
    cases l with
    | vertexBall w =>
        have hdim := (isPLCellOn_section34GraphVertexCell hsub hmap
          hK'.isCombinatorialManifoldWithBoundary w).dim_le_of_subset hcell hsubP
        omega
    | tetraBall t =>
        cases section34GraphCutFamily_subset_strict_on_tetrahedra hsub hmap t (.patch p) hsubP
    | splitDisk e => exact fun x hx => Or.inr (mem_iUnion.mpr ⟨e, hx⟩)
    | faceDisk s =>
        have hst := (section34GraphResidualCell_subset_iff hsub hmap s.2.1 p.1.1.2.1
          (by omega)).mp hsubR
        exact fun x hx => Or.inl (hrim s hst hx)
    | patch q =>
        rcases section34GraphCutFamily_subset_strict_on_patches hsub hmap q (.patch p) hsubP
          with heq | hdim
        · exact (hl.2 heq).elim
        · simp only [section34Dim] at hdim
          omega
    | faceArc a =>
        obtain ⟨A, hA⟩ := exists_isPLCellOn_section34GraphVertexCell_inter_residualTriangle
          hsub hmap a.1.1 a.1.2 a.2
        obtain ⟨x, hx⟩ := hA.nonempty
        have hst := htriangle a.1.1 ⟨x, hx.2, hsubR hx⟩
        exact fun y hy => Or.inl (hrim a.1.1 hst hy.2)
    | edgeArc a => exact fun x hx => Or.inr (mem_iUnion.mpr ⟨a.1.2, hx.2⟩)
    | markedPoint a => exact fun x hx => Or.inr (mem_iUnion.mpr ⟨a.1.2, hx.1⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
