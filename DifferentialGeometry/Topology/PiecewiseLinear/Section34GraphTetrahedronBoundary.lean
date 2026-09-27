/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RefinedResidualBalls
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphVertexBoundaryCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  [FiniteDimensional ℝ Ea] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

omit [T2Space M] in
theorem section34GraphResidualCell_inter_vertex_subset_frontier
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK' : IsCombinatorialManifoldWithBoundary 3 𝒦'.complex)
    (t : Finset Ea) (w : Section34VertexIndex 𝒦 𝒦') :
    section34GraphResidualCell 𝒦 𝒦' t ∩ section34GraphVertexCell 𝒦 𝒦' w ⊆
      frontier (section34GraphResidualCell 𝒦 𝒦' t) := by
  have hC := isPLCellOn_section34GraphVertexCell hsub hmap hK' w
  have hc : IsClosed (section34GraphResidualCell 𝒦 𝒦' t) := isClosed_closure
  rw [hc.frontier_eq]
  rintro x ⟨hxR, hxC⟩
  refine ⟨hxR, fun hxi => ?_⟩
  obtain ⟨y, hyR, hyC⟩ := mem_closure_iff.mp (hC.subset_closure_interior hxC)
    _ isOpen_interior hxi
  exact section34GraphResidualCell_subset_compl_interior_vertex_union t
    (interior_subset hyR) (interior_mono (subset_iUnion (section34GraphVertexCell 𝒦 𝒦') w) hyC)

theorem section34TriangleBody_subset_frontier_tetrahedronBody
    (s : Section34SimplexIndex 𝒦 3) (t : Section34SimplexIndex 𝒦 4) (hst : s.1 ⊆ t.1) :
    simplexBody 𝒦 s.1 ⊆ frontier (simplexBody 𝒦 t.1) := by
  classical
  let S := simplexComplex t.1 (𝒦.complex.indep t.2.1)
  have hS : S.space = convexHull ℝ (t.1 : Set Ea) :=
    simplexComplex_space _ _ (𝒦.complex.nonempty_of_mem_faces t.2.1)
  have hball : IsPLBall 3 S.space := hS.symm ▸
    isPLBall_convexHull_of_affineIndependent t.1 (𝒦.complex.indep t.2.1) t.2.2
  have hcell := 𝒦.isPLCellOn_image_boundaryComplex S (simplexComplex_faces_finite _ _)
    (hS.symm ▸ 𝒦.complex.convexHull_subset_space t.2.1) (by omega) hball
  have hface : s.1 ∈ (simplexBoundary t.1 (𝒦.complex.indep t.2.1)).faces := by
    refine ⟨hst, 𝒦.complex.nonempty_of_mem_faces s.2.1, ?_⟩
    intro heq
    have := congrArg Finset.card heq
    rw [s.2.2, t.2.2] at this
    omega
  rw [hS] at hcell
  change 𝒦.map '' convexHull ℝ (s.1 : Set Ea) ⊆
    frontier (𝒦.map '' convexHull ℝ (t.1 : Set Ea))
  rw [← hcell.boundary_eq_frontier]
  change 𝒦.map '' convexHull ℝ (s.1 : Set Ea) ⊆
    𝒦.map '' (boundaryComplex 3 (simplexComplex t.1 (𝒦.complex.indep t.2.1))).space
  rw [boundaryComplex_simplexComplex
    (𝒦.complex.indep t.2.1) t.2.2]
  exact image_mono ((simplexBoundary t.1 (𝒦.complex.indep t.2.1)).convexHull_subset_space hface)

theorem section34GraphResidualTriangle_subset_frontier_tetrahedron
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s : Section34SimplexIndex 𝒦 3) (t : Section34SimplexIndex 𝒦 4) (hst : s.1 ⊆ t.1) :
    section34GraphResidualCell 𝒦 𝒦' s.1 ⊆ frontier (section34GraphResidualCell 𝒦 𝒦' t.1) := by
  have hRt : section34GraphResidualCell 𝒦 𝒦' s.1 ⊆ section34GraphResidualCell 𝒦 𝒦' t.1 :=
    (section34GraphResidualCell_subset_iff hsub hmap s.2.1 t.2.1 (by omega)).mpr hst
  have hc : IsClosed (section34GraphResidualCell 𝒦 𝒦' t.1) := isClosed_closure
  rw [hc.frontier_eq]
  intro x hx
  refine ⟨hRt hx, fun hxi => ?_⟩
  have hxf := section34TriangleBody_subset_frontier_tetrahedronBody s t hst
    (section34GraphResidualCell_subset_simplexBody s.2.1 hx)
  exact hxf.2 (interior_mono (section34GraphResidualCell_subset_simplexBody t.2.1) hxi)

theorem section34GraphResidualTetrahedron_frontier_eq_iUnion_proper_faces
    (hU : IsOpen U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    (hmap : 𝒦'.map = 𝒦.map) (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (t : Section34SimplexIndex 𝒦 4) :
    frontier (section34GraphResidualCell 𝒦 𝒦' t.1) =
      ⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.tetraBall t) \ {.tetraBall t},
        section34GraphCutFamily 𝒦 𝒦' m := by
  classical
  let C := section34GraphVertexCell 𝒦 𝒦'
  let R : Section34SimplexIndex 𝒦 4 → Set M := fun u => section34GraphResidualCell 𝒦 𝒦' u.1
  let F : Section34VertexIndex 𝒦 𝒦' ⊕ Section34SimplexIndex 𝒦 4 → Set M := Sum.elim C R
  have hC := isPLCellOn_section34GraphVertexCell hsub hmap
    hK'.isCombinatorialManifoldWithBoundary
  have hF : ∀ i, IsClosed (F i) := by
    rintro (v | u)
    · exact (hC v).isCompact.isClosed
    · exact isClosed_closure
  have hcover : (⋃ i, F i) = U := by
    rw [iUnion_sum]
    exact (eq_iUnion_section34GraphVertexCell_union_residuals 𝒦 𝒦' hK).symm
  have hlocal : ∀ x ∈ U, ∃ V ∈ 𝓝 x, {i | (F i ∩ V).Nonempty}.Finite := by
    intro x hx
    obtain ⟨V, hV, hfV⟩ := locallyFinite_section34GraphVertexCell 𝒦 𝒦' x hx
    obtain ⟨W, hW, hfW⟩ := locallyFinite_section34GraphResidualCell 𝒦 𝒦' 4 x hx
    refine ⟨V ∩ W, Filter.inter_mem hV hW, ?_⟩
    apply ((hfV.image Sum.inl).union (hfW.image Sum.inr)).subset
    rintro (v | u) ⟨y, hy, hyV, hyW⟩
    · exact Or.inl ⟨v, ⟨y, hy, hyV⟩, rfl⟩
    · exact Or.inr ⟨u, ⟨y, hy, hyW⟩, rfl⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp
      (frontier_subset_iUnion_of_locallyFinite_closed_cover hU F hF hcover hlocal (.inr t) hx)
    have hxR : x ∈ R t := isClosed_closure.frontier_subset hx
    rcases i with w | u
    · have hwt := (section34GraphVertexCell_inter_simplexBody_nonempty_iff
        hsub hmap w t.2.1).mp
          ⟨x, hxi, section34GraphResidualCell_subset_simplexBody t.2.1 hxR⟩
      let p : Section34PatchIndex 𝒦 𝒦' := ⟨(t, w), hwt⟩
      exact mem_iUnion₂.mpr ⟨.patch p, ⟨inter_subset_left, by simp⟩, hxR, hxi⟩
    · have hut : u ≠ t := fun heq => hi (congrArg Sum.inr heq)
      have hxI : x ∈ section34GraphResidualCell 𝒦 𝒦' (u.1 ∩ t.1) :=
        (section34GraphResidualCell_inter hsub hmap u.2.1 t.2.1).subset ⟨hxi, hxR⟩
      have hne : (u.1 ∩ t.1).Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty.mp he] at hxI
        simp [section34GraphResidualCell, simplexBody] at hxI
      have hface := 𝒦.complex.down_closed u.2.1 Finset.inter_subset_left hne
      have hcard : (u.1 ∩ t.1).card = 3 := by
        have hlt : (u.1 ∩ t.1).card < 4 := by
          have hn : u.1 ∩ t.1 ≠ u.1 := by
            intro he
            have hut' : u.1 ⊆ t.1 := he ▸ Finset.inter_subset_right
            exact hut (Subtype.ext (Finset.eq_of_subset_of_card_le hut' (by rw [u.2.2, t.2.2])))
          have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.inter_subset_left, hn⟩)
          omega
        by_contra h3
        have hem := section34GraphResidualCell_eq_empty_of_card_le_two hsub hmap hface
          (by omega)
        rw [hem] at hxI
        exact hxI
      let s : Section34SimplexIndex 𝒦 3 := ⟨u.1 ∩ t.1, hface, hcard⟩
      have hsR := (section34GraphResidualCell_subset_iff hsub hmap s.2.1 t.2.1
        (by omega)).mpr Finset.inter_subset_right
      exact mem_iUnion₂.mpr ⟨.faceDisk s, ⟨hsR, by simp⟩, hxI⟩
  · refine iUnion₂_subset fun l hl => ?_
    have hsubR : section34GraphCutFamily 𝒦 𝒦' l ⊆ section34GraphResidualCell 𝒦 𝒦' t.1 := hl.1
    have hV : ∀ w x, x ∈ section34GraphVertexCell 𝒦 𝒦' w →
        x ∈ section34GraphResidualCell 𝒦 𝒦' t.1 →
        x ∈ frontier (section34GraphResidualCell 𝒦 𝒦' t.1) := fun w x hxC hxR =>
      section34GraphResidualCell_inter_vertex_subset_frontier hsub hmap
        hK'.isCombinatorialManifoldWithBoundary t.1 w ⟨hxR, hxC⟩
    have hE : ∀ e x, x ∈ section34GraphSplitCell 𝒦 𝒦' e →
        x ∈ section34GraphResidualCell 𝒦 𝒦' t.1 →
        x ∈ frontier (section34GraphResidualCell 𝒦 𝒦' t.1) := by
      intro e x hxe hxR
      obtain ⟨w, z, -, -, heq⟩ := exists_section34GraphSplitCell_endpoints hsub hmap e
      exact hV w x (heq.subset hxe).1 hxR
    cases l with
    | vertexBall w => exact fun x hx => hV w x hx (hsubR hx)
    | tetraBall u =>
        exact (hl.2 (congrArg Section34Label.tetraBall
          ((section34GraphResidualTetrahedron_subset_iff hsub hmap u t).mp hsubR))).elim
    | splitDisk e => exact fun x hx => hE e x hx (hsubR hx)
    | faceDisk s =>
        exact section34GraphResidualTriangle_subset_frontier_tetrahedron hsub hmap s t
          ((section34GraphResidualCell_subset_iff hsub hmap s.2.1 t.2.1 (by omega)).mp hsubR)
    | patch p => exact fun x hx => hV p.1.2 x hx.2 (hsubR hx)
    | faceArc a => exact fun x hx => hV a.1.2 x hx.1 (hsubR hx)
    | edgeArc i => exact fun x hx => hE i.1.2 x hx.2 (hsubR hx)
    | markedPoint p => exact fun x hx => hE p.1.2 x hx.1 (hsubR hx)

theorem isPLCellOn_section34GraphResidualTetrahedron_proper_faces
    (hU : IsOpen U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    (hmap : 𝒦'.map = 𝒦.map) (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (t : Section34SimplexIndex 𝒦 4) :
    IsPLCellOn 3 (section34GraphResidualCell 𝒦 𝒦' t.1)
      (⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.tetraBall t) \ {.tetraBall t},
        section34GraphCutFamily 𝒦 𝒦' m) := by
  obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphResidualTetrahedron hsub hmap t
  rwa [hB.boundary_eq_frontier,
    section34GraphResidualTetrahedron_frontier_eq_iUnion_proper_faces hU hsub hmap hK hK'] at hB

end DifferentialGeometry.Topology.PiecewiseLinear
