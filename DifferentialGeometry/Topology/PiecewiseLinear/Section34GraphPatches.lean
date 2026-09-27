/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphPatchTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphFaceArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCutIntersections
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnDimensionOrder

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem exists_isPLCellOn_section34GraphVertexCell_inter_residualTetrahedron
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦')
    (hwt : Section34Incident w.1 t.1) :
    ∃ B, IsPLCellOn 2 (section34GraphVertexCell 𝒦 𝒦' w ∩
      section34GraphResidualCell 𝒦 𝒦' t.1) B := by
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
  have hball := hS.isCombinatorialManifoldWithBoundary.isPLBall_graphDualCell_inter_residual
    S G hGB hcard hvG
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
  have hraw : IsPLBall 2 ((graphDualCell 𝒦'.complex L v).space ∩ C) := by
    rw [← inter_eq_right.mpr hCS, ← inter_assoc,
      graphDualCell_space_inter_subcomplex 𝒦'.complex S L (restrict_faces_subset _ _) hvS]
    have hg : graphDualCell S G v = graphDualCell S L v :=
      graphDualCell_restrict_core_eq 𝒦'.complex S L
        (restrict_faces_subset _ _) (restrict_faces_subset _ _) v
    rw [hg] at hball
    simpa only [C, hres] using hball
  obtain ⟨Bd, hBd⟩ := 𝒦'.exists_isPLCellOn_image (inter_subset_left.trans hvertex) (by omega)
    hraw
  rw [𝒦'.bijOn.injOn.image_inter hvertex hCK,
    image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap t.2.1] at hBd
  exact ⟨Bd, hBd⟩

open Classical in
theorem section34GraphCutFamily_subset_strict_on_patches
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (p : Section34PatchIndex 𝒦 𝒦') (l : Section34CutLabelOf 𝒦 𝒦')
    (h : section34GraphCutFamily 𝒦 𝒦' (.patch p) ⊆ section34GraphCutFamily 𝒦 𝒦' l) :
    (.patch p : Section34CutLabelOf 𝒦 𝒦') = l ∨ 2 < section34Dim l := by
  classical
  let P := section34GraphCutFamily 𝒦 𝒦' (.patch p)
  let C := section34GraphVertexCell 𝒦 𝒦'
  let R := section34GraphResidualCell 𝒦 𝒦'
  let E := section34GraphSplitCell 𝒦 𝒦'
  obtain ⟨Bd, hP⟩ := exists_isPLCellOn_section34GraphVertexCell_inter_residualTetrahedron
    hsub hmap p.1.1 p.1.2 p.2
  have hcell : IsPLCellOn 2 P Bd := by
    simpa only [P, section34GraphCutFamily, inter_comm] using hP
  have hPC : P ⊆ C p.1.2 := inter_subset_right
  have hPR : P ⊆ R p.1.1.1 := inter_subset_left
  have hPE : ∀ e, ¬ P ⊆ E e := by
    intro e hPE
    have het : Section34Incident e.1 p.1.1.1 := by
      by_contra hnot
      obtain ⟨x, hx⟩ := hcell.nonempty
      have hx' : x ∈ R p.1.1.1 ∩ E e := ⟨hPR hx, hPE hx⟩
      rw [section34GraphResidualCell_inter_split_eq_empty_of_not_incident
        hsub hmap p.1.1.2.1 e hnot] at hx'
      exact hx'
    obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphSplitCell_inter_residualTetrahedron
      hsub hmap p.1.1 e het
    have hdim := hcell.dim_le_of_subset hB (subset_inter hPE hPR)
    omega
  have hPF : ∀ s : Section34SimplexIndex 𝒦 3, ¬ P ⊆ R s.1 := by
    intro s hPF
    have hws : Section34Incident p.1.2.1 s.1 := by
      by_contra hnot
      obtain ⟨x, hx⟩ := hcell.nonempty
      have hx' : x ∈ R s.1 ∩ C p.1.2 := ⟨hPF hx, hPC hx⟩
      rw [section34GraphResidualCell_inter_vertex_eq_empty_of_not_incident
        hsub hmap s.2.1 p.1.2 hnot] at hx'
      exact hx'
    obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphVertexCell_inter_residualTriangle
      hsub hmap s p.1.2 hws
    have hdim := hcell.dim_le_of_subset hB (subset_inter hPC hPF)
    omega
  have hPV : ∀ w, P ⊆ C w → p.1.2 = w := by
    intro w hPw
    by_contra hne
    obtain ⟨x, hx⟩ := hcell.nonempty
    obtain ⟨e, -, he⟩ := exists_section34GraphSplitCell_of_vertex_inter_nonempty
      hsub hmap p.1.2 w hne ⟨x, hPC hx, hPw hx⟩
    apply hPE e
    change P ⊆ section34GraphSplitCell 𝒦 𝒦' e
    rw [he]
    exact subset_inter hPC hPw
  have hPT : ∀ t : Section34SimplexIndex 𝒦 4, P ⊆ R t.1 → p.1.1 = t := by
    intro t hPt
    by_contra hne
    let q := p.1.1.1 ∩ t.1
    have hPq : P ⊆ R q :=
      (subset_inter hPR hPt).trans (section34GraphResidualCell_inter hsub hmap
        p.1.1.2.1 t.2.1).subset
    have hqneq : q ≠ p.1.1.1 := by
      intro heq
      have hst : p.1.1.1 ⊆ t.1 := heq ▸ Finset.inter_subset_right
      exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le hst
        (by rw [p.1.1.2.2, t.2.2])))
    have hqcard : q.card ≤ 3 := by
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.inter_subset_left, hqneq⟩)
      change q.card < p.1.1.1.card at hlt
      rw [p.1.1.2.2] at hlt
      omega
    rcases q.eq_empty_or_nonempty with hq | hq
    · obtain ⟨x, hx⟩ := hcell.nonempty
      have hx' := hPq hx
      simp only [hq, R, section34GraphResidualCell, simplexBody, Finset.coe_empty,
        convexHull_empty, image_empty, empty_sdiff, closure_empty, mem_empty_iff_false] at hx'
    · have hqK : q ∈ 𝒦.complex.faces :=
        𝒦.complex.down_closed p.1.1.2.1 Finset.inter_subset_left hq
      by_cases hqsmall : q.card ≤ 2
      · obtain ⟨x, hx⟩ := hcell.nonempty
        have hx' := hPq hx
        change x ∈ section34GraphResidualCell 𝒦 𝒦' q at hx'
        rw [section34GraphResidualCell_eq_empty_of_card_le_two hsub hmap hqK hqsmall] at hx'
        exact hx'
      · exact hPF ⟨q, hqK, by omega⟩ hPq
  cases l with
  | vertexBall w => exact Or.inr (by simp only [section34Dim]; omega)
  | tetraBall t => exact Or.inr (by simp only [section34Dim]; omega)
  | splitDisk e => exact (hPE e h).elim
  | faceDisk s => exact (hPF s h).elim
  | patch q =>
      have ht := hPT q.1.1 (h.trans inter_subset_left)
      have hw := hPV q.1.2 (h.trans inter_subset_right)
      exact Or.inl (congrArg Section34Label.patch (Subtype.ext (Prod.ext ht hw)))
  | faceArc a => exact (hPF a.1.1 (h.trans inter_subset_right)).elim
  | edgeArc a => exact (hPE a.1.2 (h.trans inter_subset_right)).elim
  | markedPoint a => exact (hPE a.1.2 (h.trans inter_subset_left)).elim

end DifferentialGeometry.Topology.PiecewiseLinear
