/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryBallFamilyComplement
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphBoundaryDisks
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphEdgeArcs

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLBall_closure_sdiff_derivedNeighborhood_boundary_graph
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    (hL : L.faces ⊆ (boundaryComplex 3 K).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) :
    IsPLBall 3 (closure (K.space \ (derivedNeighborhood K L).space)) := by
  classical
  have hLK := hL.trans (boundaryComplex_faces_subset 3 K)
  let _ : Finite L.faces := ((Set.toFinite K.faces).subset hLK).to_subtype
  let _ : Finite L.vertices := (SimplicialComplex.finite_vertices L).to_subtype
  let _ : Fintype L.vertices := Fintype.ofFinite _
  let _ : Finite (boundaryComplex 3 K).faces :=
    (boundaryComplex_faces_finite 3 K).to_subtype
  let C := fun v : L.vertices => graphDualCell K L v.1
  let _ : ∀ v : L.vertices, Finite (C v).faces :=
    fun v => (graphDualCell_faces_finite K L v.1).to_subtype
  have hC (v : L.vertices) : IsPLBall 3 (C v).space :=
    hK.isCombinatorialManifoldWithBoundary.isPLBall_graphDualCell K L hLK hcard v.2
  have hCK (v : L.vertices) : (C v).space ⊆ K.space :=
    (graphDualCell_space_subset K L v.1).trans (derivedNeighborhood_space_subset K L)
  have hB (v : L.vertices) : IsPLBall 2 ((C v).space ∩ (boundaryComplex 3 K).space) :=
    hK.isCombinatorialManifoldWithBoundary.isPLBall_graphDualCell_inter_boundary K L hL hcard v.2
  have hI (v w : L.vertices) (hvw : v ≠ w) :
      Disjoint (C v).space (C w).space ∨
        IsPLBall 2 ((C v).space ∩ (C w).space) ∧
          IsPLBall 1 ((C v).space ∩ (C w).space ∩ (boundaryComplex 3 K).space) := by
    have hvw' : v.1 ≠ w.1 := fun h => hvw (Subtype.ext h)
    by_cases he : {v.1, w.1} ∈ L.faces
    · right
      rw [graphDualCell_space_inter K L hLK hcard hvw' he]
      refine ⟨hK.isCombinatorialManifoldWithBoundary.isPLBall_splittingDisk K
        (hLK he) (Finset.card_pair hvw') (by omega), ?_⟩
      rw [splittingDisk_space_inter_subcomplex K (boundaryComplex 3 K)
        (boundaryComplex_faces_subset 3 K) (hL he)]
      have hBd := (isCombinatorialManifold_boundaryComplex K
        hK.isCombinatorialManifoldWithBoundary).isCombinatorialManifoldWithBoundary
      exact hBd.isPLBall_splittingDisk _ (hL he) (Finset.card_pair hvw') (by omega)
    · exact Or.inl (disjoint_iff_inter_eq_empty.mpr
        (graphDualCell_space_inter_eq_empty K L hLK hcard v.2 w.2 hvw' he))
  have htriple (v w z : L.vertices) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
      (C v).space ∩ (C w).space ∩ (C z).space = ∅ := by
    have hvw' : v.1 ≠ w.1 := fun h => hvw (Subtype.ext h)
    have hvz' : v.1 ≠ z.1 := fun h => hvz (Subtype.ext h)
    have hwz' : w.1 ≠ z.1 := fun h => hwz (Subtype.ext h)
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨hxv, hxw⟩, hxz⟩
    have hedge (y : L.vertices) (hvy : v.1 ≠ y.1) (hxy : x ∈ (C y).space) :
        {v.1, y.1} ∈ L.faces := by
      by_contra he
      have hx : x ∈ (C v).space ∩ (C y).space := ⟨hxv, hxy⟩
      rw [graphDualCell_space_inter_eq_empty K L hLK hcard v.2 y.2 hvy he] at hx
      exact hx
    have hew := hedge w hvw' hxw
    have hez := hedge z hvz' hxz
    have hne : ({v.1, w.1} : Finset E) ≠ {v.1, z.1} := by
      intro heq
      have hw : w.1 ∈ ({v.1, z.1} : Finset E) :=
        heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self w.1)
      rcases Finset.mem_insert.mp hw with hw | hw
      · exact hvw' hw.symm
      · exact hwz' (Finset.mem_singleton.mp hw)
    exact disjoint_left.mp (disjoint_splittingDisk_space K (hLK hew) (hLK hez) hne
      ((Finset.card_pair hvw').trans (Finset.card_pair hvz').symm))
      ((graphDualCell_space_inter K L hLK hcard hvw' hew).subset ⟨hxv, hxw⟩)
      ((graphDualCell_space_inter K L hLK hcard hvz' hez).subset ⟨hxv, hxz⟩)
  obtain ⟨R, -, hR, hRspace, -⟩ := exists_isPLBall_complement_of_finite_boundary_ball_family
    K hK C hC hCK hB hI htriple Finset.univ
  have hcover : (⋃ v : L.vertices, (C v).space) = (derivedNeighborhood K L).space := by
    change (⋃ v : L.vertices, (graphDualCell K L v.1).space) = _
    rw [iUnion_subtype]
    exact iUnion_graphDualCell_space K L hLK
  simpa only [Finset.mem_univ, iUnion_true, hcover, hRspace] using hR

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

open Classical in
theorem isPLBall_closure_tetrahedron_sdiff_graph_derivedNeighborhood_of_subdivision
    {T T' : LocallyFinitePLPieceIn E 3 M U}
    (hsub : IsSubdivision T'.complex T.complex) (hmap : T'.map = T.map)
    (t : Section34SimplexIndex T 4) :
    IsPLBall 3 (closure (convexHull ℝ (t.1 : Set E) \
      (derivedNeighborhood T'.complex
        (restrict T'.complex (T'.map ⁻¹' graphSkeletonSpace T))).space)) := by
  classical
  let S₀ := simplexComplex t.1 (T.complex.indep t.2.1)
  let B₀ := simplexBoundary t.1 (T.complex.indep t.2.1)
  let S := restrict T'.complex (convexHull ℝ (t.1 : Set E))
  let L₀ := restrict T.complex (T.map ⁻¹' graphSkeletonSpace T)
  let L := restrict T'.complex (T'.map ⁻¹' graphSkeletonSpace T)
  let G := restrict L S.space
  have hS₀space : S₀.space = convexHull ℝ (t.1 : Set E) :=
    simplexComplex_space _ _ (T.complex.nonempty_of_mem_faces t.2.1)
  have hS₀K : S₀.faces ⊆ T.complex.faces :=
    fun _ ht => T.complex.down_closed t.2.1 ht.2 ht.1
  have hSsub : IsSubdivision S S₀ := by
    simpa only [hS₀space] using hsub.restrict S₀ hS₀K
  have hSspace : S.space = convexHull ℝ (t.1 : Set E) := hSsub.space_eq.trans hS₀space
  have hS₀ : IsPLBall 3 S₀.space := hS₀space.symm ▸
    isPLBall_convexHull_of_affineIndependent t.1 (T.complex.indep t.2.1) t.2.2
  have hS : IsPLBall 3 S.space := hSsub.space_eq.symm ▸ hS₀
  let _ : Finite S₀.faces := (simplexComplex_faces_finite _ _).to_subtype
  let _ : Finite S.faces := (T'.restrict_faces_finite_of_isCompact
    (t.1.finite_toSet.isCompact_convexHull ℝ)
      ((T.complex.convexHull_subset_space t.2.1).trans hsub.space_eq.symm.subset)).to_subtype
  have hSbd : (boundaryComplex 3 S).space = B₀.space := by
    rw [boundaryComplex_space_of_isSubdivision S₀ S hS₀.isCombinatorialManifoldWithBoundary
      hSsub, show boundaryComplex 3 S₀ = B₀ from
        boundaryComplex_simplexComplex (T.complex.indep t.2.1) t.2.2]
  have hcore := isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap
  have hGS : G.faces ⊆ S.faces := fun f hf =>
    ((mem_restrict_faces_iff_of_faces_subset T'.complex L S
      (restrict_faces_subset _ _) (restrict_faces_subset _ _)).mp hf).2
  have hGB : G.faces ⊆ (boundaryComplex 3 S).faces := by
    intro f hf
    have hfS := hGS hf
    have hcen : f.centroid ℝ id ∈ convexHull ℝ (f : Set E) :=
      f.centroid_mem_convexHull (T'.complex.nonempty_of_mem_faces hfS.1)
    have hxL : f.centroid ℝ id ∈ L₀.space :=
      hcore.space_eq ▸ L.convexHull_subset_space hf.1 hcen
    obtain ⟨q, hq, hxq⟩ := L₀.mem_space_iff.mp hxL
    obtain ⟨hqK, hqcard⟩ := (mem_restrict_preimage_graphSkeletonSpace_iff T).mp hq
    have hxqt : f.centroid ℝ id ∈ convexHull ℝ ((q ∩ t.1 : Finset E) : Set E) := by
      rw [Finset.coe_inter, ← T.complex.convexHull_inter_convexHull hqK t.2.1]
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
      (centroid_mem_openSimplex (T'.complex.nonempty_of_mem_faces hfS.1))
    rw [hSbd]
    exact B₀.convexHull_subset_space hqB hxqt
  have hGcard : ∀ f ∈ G.faces, f.card ≤ 2 := fun _ hf =>
    hcore.card_le (fun q hq => ((mem_restrict_preimage_graphSkeletonSpace_iff T).mp hq).2) hf.1
  have hres : closure (convexHull ℝ (t.1 : Set E) \ (derivedNeighborhood T'.complex L).space) =
      closure (S.space \ (derivedNeighborhood S G).space) := by
    congr 1
    rw [show G = restrict L S.space from rfl,
      derivedNeighborhood_restrict_core_eq T'.complex S L
        (restrict_faces_subset _ _) (restrict_faces_subset _ _),
      ← derivedNeighborhood_space_inter_subcomplex T'.complex S L (restrict_faces_subset _ _),
      hSspace]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hres]
  exact isPLBall_closure_sdiff_derivedNeighborhood_boundary_graph S G hS hGB hGcard

theorem exists_isPLCellOn_section34GraphResidualTetrahedron
    {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
    [T2Space M] {T T' : LocallyFinitePLPieceIn Ea 3 M U}
    (hsub : IsSubdivision T'.complex T.complex) (hmap : T'.map = T.map)
    (t : Section34SimplexIndex T 4) :
    ∃ B, IsPLCellOn 3 (section34GraphResidualCell T T' t.1) B := by
  classical
  let N := (derivedNeighborhood T'.complex
    (restrict T'.complex (T'.map ⁻¹' graphSkeletonSpace T))).space
  have hball := isPLBall_closure_tetrahedron_sdiff_graph_derivedNeighborhood_of_subdivision
    hsub hmap t
  have hcl : closure (convexHull ℝ (t.1 : Set Ea) \ N) ⊆ convexHull ℝ (t.1 : Set Ea) :=
    closure_minimal sdiff_subset (t.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  obtain ⟨B, hB⟩ := T'.exists_isPLCellOn_image
    (hcl.trans ((T.complex.convexHull_subset_space t.2.1).trans hsub.space_eq.symm.subset))
    (by omega) hball
  rw [image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap t.2.1] at hB
  exact ⟨B, hB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
