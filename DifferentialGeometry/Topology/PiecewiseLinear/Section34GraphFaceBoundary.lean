/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplementCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphArcSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_residual_disk_boundary_eq_inter_derivedNeighborhood
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧ IsPLBall 2 R.space ∧
      R.space = closure (K.space \ (derivedNeighborhood K (boundaryComplex 2 K)).space) ∧
      (boundaryComplex 2 R).space =
        R.space ∩ (derivedNeighborhood K (boundaryComplex 2 K)).space := by
  classical
  let B := boundaryComplex 2 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 2 K).to_subtype
  have hB : IsPLSphere 1 B.space := isPLSphere_boundaryComplex_space_of_isPLBall K hK
  obtain ⟨ρ, hρ⟩ := exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle K B
    hK.isCombinatorialManifoldWithBoundary (boundaryComplex_faces_subset 2 K)
    hB.isCombinatorialManifold hB.isConnected (isOrientable_of_isPLBall hK)
  have hJ : IsPLSphere 1 (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  obtain ⟨A, hAfin, hA, -, hAN, -⟩ := hρ.exists_annulus_complex hJ zero_lt_one
  let _ : Finite A.faces := hAfin.to_subtype
  have hball := isPLBall_closure_sdiff_derivedNeighborhood_boundaryComplex K hK
  obtain ⟨R, hRfin, hRspace⟩ := hball.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsPLBall 2 R.space := hRspace.symm ▸ hball
  refine ⟨R, hRfin, hR, hRspace, ?_⟩
  have hbd := boundaryComplex_space_of_closure_sdiff_of_boundary_subset K A R
    hK.isCombinatorialManifoldWithBoundary hA
    (hAN.symm ▸ derivedNeighborhood_space_subset K B) hR.isCombinatorialManifoldWithBoundary
    (by simpa only [hAN] using hRspace)
    (hAN.symm ▸ subcomplex_space_subset_derivedNeighborhood
      (boundaryComplex_faces_subset 2 K))
  simpa only [hAN] using hbd

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem exists_isPLCellOn_section34GraphResidualTriangle_boundary
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s : Section34SimplexIndex 𝒦 3) :
    ∃ B, IsPLCellOn 2 (section34GraphResidualCell 𝒦 𝒦' s.1) B ∧
      B = section34GraphResidualCell 𝒦 𝒦' s.1 ∩
        ⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w := by
  classical
  let S₀ := simplexComplex s.1 (𝒦.complex.indep s.2.1)
  let B₀ := simplexBoundary s.1 (𝒦.complex.indep s.2.1)
  let S := restrict 𝒦'.complex (convexHull ℝ (s.1 : Set Ea))
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  let L₀ := restrict 𝒦.complex (𝒦.map ⁻¹' graphSkeletonSpace 𝒦)
  let N := (derivedNeighborhood 𝒦'.complex L).space
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
      (fun _ hs => ((mem_restrict_faces_iff_of_faces_subset 𝒦'.complex L S
        (restrict_faces_subset _ _) (restrict_faces_subset _ _)).mp hs).2)
      (boundaryComplex_faces_subset 2 S)
      ((restrict_space_eq_inter_of_faces_subset 𝒦'.complex L S
        (restrict_faces_subset _ _) (restrict_faces_subset _ _)).trans hcore)
  have hNlocal : (derivedNeighborhood S (boundaryComplex 2 S)).space = N ∩ S.space := by
    rw [← hLS, derivedNeighborhood_restrict_core_eq 𝒦'.complex S L
      (restrict_faces_subset _ _) (restrict_faces_subset _ _),
      derivedNeighborhood_space_inter_subcomplex 𝒦'.complex S L (restrict_faces_subset _ _)]
  obtain ⟨R, hRfin, hR, hRspace, hRbd⟩ :=
    exists_residual_disk_boundary_eq_inter_derivedNeighborhood S hS
  let _ : Finite R.faces := hRfin.to_subtype
  have hReq : R.space = closure (convexHull ℝ (s.1 : Set Ea) \ N) := by
    rw [hRspace, hNlocal, hSspace]
    congr 1
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hRS : R.space ⊆ S.space := by
    rw [hRspace]
    exact closure_minimal sdiff_subset (isPolyhedron_space S).isClosed
  have hRK := hRS.trans (space_mono_of_faces_subset (restrict_faces_subset _ _))
  have himage : 𝒦'.map '' R.space = section34GraphResidualCell 𝒦 𝒦' s.1 := by
    rw [hReq]
    exact image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap s.2.1
  have hcell := 𝒦'.isPLCellOn_image_boundaryComplex R hRfin hRK (by omega) hR
  refine ⟨𝒦'.map '' (boundaryComplex 2 R).space, himage ▸ hcell, ?_⟩
  rw [hRbd, hNlocal, ← inter_assoc, inter_eq_left.mpr (inter_subset_left.trans hRS),
    𝒦'.bijOn.injOn.image_inter hRK (derivedNeighborhood_space_subset 𝒦'.complex L), himage,
    iUnion_section34GraphVertexCell]

theorem isPLCellOn_section34GraphResidualTriangle_proper_faces
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s : Section34SimplexIndex 𝒦 3) :
    IsPLCellOn 2 (section34GraphResidualCell 𝒦 𝒦' s.1)
      (⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.faceDisk s) \ {.faceDisk s},
        section34GraphCutFamily 𝒦 𝒦' m) := by
  classical
  obtain ⟨B, hB, hBeq⟩ := exists_isPLCellOn_section34GraphResidualTriangle_boundary hsub hmap s
  have hE : ∀ e : Section34EdgeIndex 𝒦 𝒦', section34GraphSplitCell 𝒦 𝒦' e ⊆
      ⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w := by
    intro e
    obtain ⟨w, z, -, -, heq⟩ := exists_section34GraphSplitCell_endpoints hsub hmap e
    exact (heq.subset.trans inter_subset_left).trans
      (subset_iUnion (section34GraphVertexCell 𝒦 𝒦') w)
  suffices B = ⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.faceDisk s) \ {.faceDisk s},
      section34GraphCutFamily 𝒦 𝒦' m by rw [← this]; exact hB
  rw [hBeq]
  apply Subset.antisymm
  · rintro x ⟨hxR, hxN⟩
    obtain ⟨w, hxw⟩ := mem_iUnion.mp hxN
    have hws := (section34GraphVertexCell_inter_simplexBody_nonempty_iff hsub hmap w s.2.1).mp
      ⟨x, hxw, section34GraphResidualCell_subset_simplexBody s.2.1 hxR⟩
    let a : Section34ArcIndex 𝒦 𝒦' := ⟨(s, w), hws⟩
    exact mem_iUnion₂.mpr ⟨.faceArc a, ⟨inter_subset_right, by simp⟩, hxw, hxR⟩
  · refine iUnion₂_subset fun l hl => ?_
    have hsubR : section34GraphCutFamily 𝒦 𝒦' l ⊆ section34GraphResidualCell 𝒦 𝒦' s.1 := hl.1
    have hne : l ≠ .faceDisk s := hl.2
    refine subset_inter hsubR ?_
    cases l with
    | vertexBall w => exact subset_iUnion (section34GraphVertexCell 𝒦 𝒦') w
    | tetraBall t =>
        cases section34GraphCutFamily_subset_strict_on_tetrahedra hsub hmap t (.faceDisk s) hsubR
    | splitDisk e => exact hE e
    | faceDisk t =>
        exact (hne (congrArg Section34Label.faceDisk
          ((section34GraphResidualTriangle_subset_iff hsub hmap t s).mp hsubR))).elim
    | patch p =>
        exact inter_subset_right.trans (subset_iUnion (section34GraphVertexCell 𝒦 𝒦') p.1.2)
    | faceArc a =>
        exact inter_subset_left.trans (subset_iUnion (section34GraphVertexCell 𝒦 𝒦') a.1.2)
    | edgeArc i => exact inter_subset_right.trans (hE i.1.2)
    | markedPoint p => exact inter_subset_left.trans (hE p.1.2)

end DifferentialGeometry.Topology.PiecewiseLinear
