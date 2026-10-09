/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphFaceArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphArcSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnDimensionOrder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphPatches
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualSeparation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem LocallyFinitePLPieceIn.isPLCellOn_image_of_isPLHomeomorphOn_Icc
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {U : Set M} (T : LocallyFinitePLPieceIn E 3 M U) {P : Set E} {γ : ℝ → E}
    (hsub : P ⊆ T.complex.space) (hγ : IsPLHomeomorphOn γ (Icc 0 1) P) :
    IsPLCellOn 1 (T.map '' P) {T.map (γ 0), T.map (γ 1)} := by
  let f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
  have hbij : BijOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) (Icc 0 1) := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun t ht => ?_⟩
    · have hsum : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
      exact ⟨hx.1 1, by change x 1 ≤ 1; linarith [hx.1 0]⟩
    · have hsumx : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
      have hsumy : y 0 + y 1 = 1 := by simpa [Fin.sum_univ_two] using hy.2
      change x 1 = y 1 at hxy
      funext i
      fin_cases i
      · change x 0 = y 0
        linarith
      · exact hxy
    · refine ⟨![1 - t, t], ⟨?_, ?_⟩, rfl⟩
      · intro i
        fin_cases i
        · change 0 ≤ 1 - t
          linarith [ht.2]
        · exact ht.1
      · simp [Fin.sum_univ_two]
  have hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) (Icc 0 1) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (isHPolytope_stdSimplex (Fin 2)).isPolyhedron
      ((isPiecewiseAffineOn_of_affine f.toAffineMap isOpen_univ).mono_of_isPolyhedron
        (isHPolytope_stdSimplex (Fin 2)).isPolyhedron (subset_univ _)) hbij
  have hball : IsPLBall 1 P := ⟨γ ∘ f, hf.trans hγ⟩
  obtain ⟨L, hfin, hLP⟩ := hball.isPolyhedron.exists_simplicialComplex
  have hcell := T.isPLCellOn_image_stdSimplexBoundary L hfin (hLP.symm ▸ hsub)
    (by omega) (hLP.symm ▸ hf.trans hγ)
  simpa [hLP, stdSimplexBoundary_one_eq_pair, image_pair, f] using hcell

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem isPLCellOn_section34GraphFaceArc_with_marked_boundary
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (hws : Section34Incident w.1 s.1) :
    IsPLCellOn 1 (section34GraphVertexCell 𝒦 𝒦' w ∩
      section34GraphResidualCell 𝒦 𝒦' s.1)
      (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : Section34Incident e.1 s.1) (_ : w.1 ⊆ e.1),
        section34GraphSplitCell 𝒦 𝒦' e ∩ section34GraphResidualCell 𝒦 𝒦' s.1) := by
  classical
  let S₀ := simplexComplex s.1 (𝒦.complex.indep s.2.1)
  let B₀ := simplexBoundary s.1 (𝒦.complex.indep s.2.1)
  let S := restrict 𝒦'.complex (convexHull ℝ (s.1 : Set Ea))
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  let L₀ := restrict 𝒦.complex (𝒦.map ⁻¹' graphSkeletonSpace 𝒦)
  have hS₀space : S₀.space = convexHull ℝ (s.1 : Set Ea) :=
    simplexComplex_space _ _ (𝒦.complex.nonempty_of_mem_faces s.2.1)
  have hS₀K : S₀.faces ⊆ 𝒦.complex.faces :=
    fun _ ht => 𝒦.complex.down_closed s.2.1 ht.2 ht.1
  have hSsub : IsSubdivision S S₀ := by
    simpa only [hS₀space] using hsub.restrict S₀ hS₀K
  have hSspace : S.space = convexHull ℝ (s.1 : Set Ea) := hSsub.space_eq.trans hS₀space
  have hS₀ : IsPLBall 2 S₀.space := hS₀space.symm ▸
    isPLBall_convexHull_of_affineIndependent s.1 (𝒦.complex.indep s.2.1) s.2.2
  have hS : IsPLBall 2 S.space := hSsub.space_eq.symm ▸ hS₀
  let _ : Finite S₀.faces := (simplexComplex_faces_finite _ _).to_subtype
  let _ : Finite S.faces := (𝒦'.restrict_faces_finite_of_isCompact
    (s.1.finite_toSet.isCompact_convexHull ℝ)
      ((𝒦.complex.convexHull_subset_space s.2.1).trans hsub.space_eq.symm.subset)).to_subtype
  have hSbd : (boundaryComplex 2 S).space = B₀.space := by
    rw [boundaryComplex_space_of_isSubdivision S₀ S hS₀.isCombinatorialManifoldWithBoundary
      hSsub, show boundaryComplex 2 S₀ = B₀ from
        boundaryComplex_simplexComplex (𝒦.complex.indep s.2.1) s.2.2]
  have hLspace : L.space = L₀.space :=
    (isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap).space_eq
  have hcore : L.space ∩ S.space = (boundaryComplex 2 S).space := by
    rw [hSbd, hLspace, hSspace, ← hS₀space,
      ← restrict_space_eq_inter_of_faces_subset 𝒦.complex L₀ S₀
        (restrict_faces_subset _ _) hS₀K, hS₀space,
      restrict_graph_core_triangle_eq_simplexBoundary 𝒦 s]
  have hLS : restrict L S.space = boundaryComplex 2 S :=
    eq_of_faces_subset_of_space_eq _ _ S
      (fun _ hu => ((mem_restrict_faces_iff_of_faces_subset 𝒦'.complex L S
        (restrict_faces_subset _ _) (restrict_faces_subset _ _)).mp hu).2)
      (boundaryComplex_faces_subset 2 S)
      ((restrict_space_eq_inter_of_faces_subset 𝒦'.complex L S
        (restrict_faces_subset _ _) (restrict_faces_subset _ _)).trans hcore)
  let v := w.1.centroid ℝ id
  have hvS : {v} ∈ S.faces := by
    rw [show ({v} : Finset Ea) = w.1 from (section34VertexIndex_eq_singleton_centroid w).symm]
    exact ⟨w.2.1, convexHull_min hws (convex_convexHull ℝ (s.1 : Set Ea))⟩
  have hvL : {v} ∈ L.faces := singleton_centroid_mem_section34GraphCore w
  have hvB : {v} ∈ (boundaryComplex 2 S).faces := by
    rw [← hLS]
    exact ⟨hvL, hSspace.symm ▸ hvS.2⟩
  have hres : closure (convexHull ℝ (s.1 : Set Ea) \
      (derivedNeighborhood 𝒦'.complex L).space) =
      closure (S.space \
        (derivedNeighborhood S (boundaryComplex 2 S)).space) := by
    congr 1
    rw [← hLS, derivedNeighborhood_restrict_core_eq 𝒦'.complex S L
      (restrict_faces_subset _ _) (restrict_faces_subset _ _),
      ← derivedNeighborhood_space_inter_subcomplex 𝒦'.complex S L (restrict_faces_subset _ _),
      hSspace]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  let C := closure (convexHull ℝ (s.1 : Set Ea) \
    (derivedNeighborhood 𝒦'.complex L).space)
  have hCS : C ⊆ S.space := hSspace.symm ▸
    closure_minimal sdiff_subset (s.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hCK : C ⊆ 𝒦'.complex.space :=
    hCS.trans (space_mono_of_faces_subset (restrict_faces_subset _ _))
  have htrace : (graphDualCell 𝒦'.complex L v).space ∩ C =
      (graphDualCell S (boundaryComplex 2 S) v).space ∩
        closure (S.space \ (derivedNeighborhood S (boundaryComplex 2 S)).space) := by
    rw [← inter_eq_right.mpr hCS, ← inter_assoc,
      graphDualCell_space_inter_subcomplex 𝒦'.complex S L (restrict_faces_subset _ _) hvS,
      ← graphDualCell_restrict_core_eq 𝒦'.complex S L
        (restrict_faces_subset _ _) (restrict_faces_subset _ _), hLS]
    exact congrArg (fun A => (graphDualCell S (boundaryComplex 2 S) v).space ∩ A) hres
  obtain ⟨γ, hγ, hpoints⟩ := exists_isPLHomeomorphOn_graphDualCell_inter_boundary_residual S hS hvB
  have hGsub : (graphDualCell 𝒦'.complex L v).space ⊆ 𝒦'.complex.space :=
    (graphDualCell_space_subset _ _ _).trans (derivedNeighborhood_space_subset _ _)
  have hcell := 𝒦'.isPLCellOn_image_of_isPLHomeomorphOn_Icc
    (inter_subset_left.trans hGsub) (htrace.symm ▸ hγ)
  rw [𝒦'.bijOn.injOn.image_inter hGsub hCK,
    image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap s.2.1] at hcell
  have hmark (e : Section34EdgeIndex 𝒦 𝒦') (heS : e.1 ∈ S.faces) :
      𝒦'.map '' ((splittingDisk S e.1 heS).space ∩
        closure (S.space \ (derivedNeighborhood S (boundaryComplex 2 S)).space)) =
      section34GraphSplitCell 𝒦 𝒦' e ∩ section34GraphResidualCell 𝒦 𝒦' s.1 := by
    rw [← image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell
      hsub hmap s.2.1]
    change _ = 𝒦'.map '' (splittingDisk 𝒦'.complex e.1 e.2.1).space ∩ 𝒦'.map '' C
    rw [← 𝒦'.bijOn.injOn.image_inter (splittingDisk_space_subset _ e.2.1) hCK]
    congr 1
    rw [← inter_eq_right.mpr hCS, ← inter_assoc,
      splittingDisk_space_inter_subcomplex 𝒦'.complex S (restrict_faces_subset _ _) heS]
    exact congrArg (fun A => (splittingDisk S e.1 heS).space ∩ A) hres.symm
  have hbd : {𝒦'.map (γ 0), 𝒦'.map (γ 1)} =
      ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : Section34Incident e.1 s.1) (_ : w.1 ⊆ e.1),
        section34GraphSplitCell 𝒦 𝒦' e ∩ section34GraphResidualCell 𝒦 𝒦' s.1 := by
    rw [← image_pair, hpoints, image_iUnion]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨d, hxd⟩ := mem_iUnion.mp hx
      have hdG : d.1 ∈ (restrict L S.space).faces := by
        rw [hLS]
        exact d.2.1
      have hdL : d.1 ∈ L.faces := hdG.1
      have hdS : d.1 ∈ S.faces := boundaryComplex_faces_subset 2 S d.2.1
      let e : Section34EdgeIndex 𝒦 𝒦' := ⟨d.1, hdL.1, d.2.2.1, by
        rintro _ ⟨y, hy, rfl⟩
        exact hdL.2 hy⟩
      have hes : Section34Incident e.1 s.1 := fun y hy =>
        hdS.2 (subset_convexHull ℝ _ hy)
      have hwe : w.1 ⊆ e.1 := by
        rw [section34VertexIndex_eq_singleton_centroid w]
        exact Finset.singleton_subset_iff.mpr d.2.2.2
      exact mem_iUnion₂.mpr ⟨e, hes, mem_iUnion.mpr ⟨hwe, (hmark e hdS).subset hxd⟩⟩
    · intro x hx
      obtain ⟨e, hes, hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨hwe, hxe⟩ := mem_iUnion.mp hx
      have heS : e.1 ∈ S.faces := ⟨e.2.1,
        convexHull_min hes (convex_convexHull ℝ (s.1 : Set Ea))⟩
      have heL : e.1 ∈ L.faces := ⟨e.2.1, fun y hy => e.2.2.2 (mem_image_of_mem _ hy)⟩
      have heB : e.1 ∈ (boundaryComplex 2 S).faces := hLS ▸
        (show e.1 ∈ (restrict L S.space).faces from ⟨heL, hSspace.symm ▸ heS.2⟩)
      have hve : v ∈ e.1 := hwe (by rw [section34VertexIndex_eq_singleton_centroid w]; simp [v])
      exact mem_iUnion.mpr ⟨⟨e.1, heB, e.2.2.1, hve⟩, (hmark e heS).symm.subset hxe⟩
  exact hbd ▸ hcell

theorem isPLCellOn_section34GraphFaceArc_proper_faces
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifold 3 𝒦'.complex) (a : Section34ArcIndex 𝒦 𝒦') :
    IsPLCellOn 1 (section34GraphCutFamily 𝒦 𝒦' (.faceArc a))
      (⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.faceArc a) \ {.faceArc a},
        section34GraphCutFamily 𝒦 𝒦' m) := by
  classical
  have hA := isPLCellOn_section34GraphFaceArc_with_marked_boundary hsub hmap a.1.1 a.1.2 a.2
  suffices (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : Section34Incident e.1 a.1.1.1)
      (_ : a.1.2.1 ⊆ e.1), section34GraphSplitCell 𝒦 𝒦' e ∩
        section34GraphResidualCell 𝒦 𝒦' a.1.1.1) =
      ⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.faceArc a) \ {.faceArc a},
        section34GraphCutFamily 𝒦 𝒦' m by
    rw [← this]
    exact hA
  apply Subset.antisymm
  · intro x hx
    obtain ⟨e, hes, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨hwe, hxe⟩ := mem_iUnion.mp hx
    let p : Section34MarkIndex 𝒦 𝒦' := ⟨(a.1.1, e), hes⟩
    refine mem_iUnion₂.mpr ⟨.markedPoint p, ⟨?_, by simp⟩, hxe⟩
    exact fun y hy => ⟨section34GraphSplitCell_subset_vertex_of_subset hsub hmap
      a.1.2 e hwe hy.1, hy.2⟩
  · refine iUnion₂_subset fun l hl => ?_
    have hLA : section34GraphCutFamily 𝒦 𝒦' l ⊆
        section34GraphCutFamily 𝒦 𝒦' (.faceArc a) := hl.1
    have hne : l ≠ .faceArc a := hl.2
    cases l with
    | vertexBall w =>
        have hd := (isPLCellOn_section34GraphVertexCell hsub hmap
          hK.isCombinatorialManifoldWithBoundary w).dim_le_of_subset hA hLA
        omega
    | tetraBall t =>
        cases section34GraphCutFamily_subset_strict_on_tetrahedra hsub hmap t (.faceArc a) hLA
    | splitDisk e =>
        have hd := (isPLCellOn_section34GraphSplitCell hK e).dim_le_of_subset hA hLA
        omega
    | faceDisk s =>
        obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphResidualTriangle hsub hmap s
        have hd := hB.dim_le_of_subset hA hLA
        omega
    | patch p =>
        rcases section34GraphCutFamily_subset_strict_on_patches hsub hmap p (.faceArc a) hLA
          with heq | hdim
        · cases heq
        · simp only [section34Dim] at hdim
          omega
    | faceArc b =>
        rcases (section34GraphCutFamily_subset_strict_on_arcs hsub hmap).1 b (.faceArc a) hLA
          with heq | hdim
        · exact (hne heq).elim
        · simp only [section34Dim] at hdim
          omega
    | edgeArc i =>
        rcases (section34GraphCutFamily_subset_strict_on_arcs hsub hmap).2 i (.faceArc a) hLA
          with heq | hdim
        · cases heq
        · simp only [section34Dim] at hdim
          omega
    | markedPoint p =>
        intro x hx
        have hxA := hLA hx
        have hs : p.1.1 = a.1.1 := by
          by_contra hs
          exact disjoint_left.mp (pairwiseDisjoint_section34GraphResidualTriangle hsub hmap hs)
            hx.2 hxA.2
        have hwe := vertex_subset_edge_of_section34GraphVertexCell_inter_splitCell_nonempty
          hsub hmap a.1.2 p.1.2 ⟨x, hxA.1, hx.1⟩
        have hes : Section34Incident p.1.2.1 a.1.1.1 := hs ▸ p.2
        exact mem_iUnion₂.mpr ⟨p.1.2, hes, mem_iUnion.mpr ⟨hwe, hx.1, hxA.2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
