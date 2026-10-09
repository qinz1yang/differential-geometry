/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteBoundaryCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCellSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  [FiniteDimensional ℝ Ea] {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

omit [FiniteDimensional ℝ Ea] [T2Space M] in
theorem section34GraphResidualCell_subset_compl_interior_vertex_union (t : Finset Ea) :
    section34GraphResidualCell 𝒦 𝒦' t ⊆
      (interior (⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w))ᶜ :=
  closure_minimal (fun _ hx => fun hi => hx.2 (interior_subset hi))
    isOpen_interior.isClosed_compl

theorem section34GraphResidualCell_inter_vertex_subset_boundary
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK' : IsCombinatorialManifoldWithBoundary 3 𝒦'.complex)
    (t : Finset Ea) (w : Section34VertexIndex 𝒦 𝒦') :
    section34GraphResidualCell 𝒦 𝒦' t ∩ section34GraphVertexCell 𝒦 𝒦' w ⊆
      section34GraphVertexBoundary 𝒦 𝒦' w := by
  have hcell := isPLCellOn_section34GraphVertexCell hsub hmap hK' w
  rw [hcell.boundary_eq_frontier, hcell.isCompact.isClosed.frontier_eq]
  intro x hx
  exact ⟨hx.2, fun hi => section34GraphResidualCell_subset_compl_interior_vertex_union t
    hx.1 (interior_mono (subset_iUnion (section34GraphVertexCell 𝒦 𝒦') w) hi)⟩

theorem section34GraphVertexBoundary_eq_iUnion_splits_union_patches
    (hU : IsOpen U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    (hmap : 𝒦'.map = 𝒦.map) (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (w : Section34VertexIndex 𝒦 𝒦') :
    section34GraphVertexBoundary 𝒦 𝒦' w =
      (⋃ e : Section34EdgeIndex 𝒦 𝒦', ⋃ (_ : w.1 ⊆ e.1),
        section34GraphSplitCell 𝒦 𝒦' e) ∪
      ⋃ t : Section34SimplexIndex 𝒦 4, ⋃ (_ : Section34Incident w.1 t.1),
        section34GraphResidualCell 𝒦 𝒦' t.1 ∩ section34GraphVertexCell 𝒦 𝒦' w := by
  classical
  let C := section34GraphVertexCell 𝒦 𝒦'
  let R : Section34SimplexIndex 𝒦 4 → Set M := fun t => section34GraphResidualCell 𝒦 𝒦' t.1
  let F : Section34VertexIndex 𝒦 𝒦' ⊕ Section34SimplexIndex 𝒦 4 → Set M := Sum.elim C R
  have hC := isPLCellOn_section34GraphVertexCell hsub hmap
    hK'.isCombinatorialManifoldWithBoundary
  have hF : ∀ i, IsClosed (F i) := by
    rintro (v | t)
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
    rintro (v | t) ⟨y, hy, hyV, hyW⟩
    · exact Or.inl ⟨v, ⟨y, hy, hyV⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨y, hy, hyW⟩, rfl⟩
  apply Subset.antisymm
  · intro x hx
    have hxf : x ∈ frontier (F (.inl w)) := (hC w).boundary_eq_frontier ▸ hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp
      (frontier_subset_iUnion_of_locallyFinite_closed_cover hU F hF hcover hlocal (.inl w) hxf)
    have hxC : x ∈ C w := (hC w).boundary_subset hx
    rcases i with v | t
    · have hwv : w ≠ v := fun heq => hi (congrArg Sum.inl heq.symm)
      obtain ⟨e, -, heq⟩ := exists_section34GraphSplitCell_of_vertex_inter_nonempty
        hsub hmap w v hwv ⟨x, hxC, hxi⟩
      have hxe : x ∈ section34GraphSplitCell 𝒦 𝒦' e := heq.symm ▸ ⟨hxC, hxi⟩
      have hwe := vertex_subset_edge_of_section34GraphVertexCell_inter_splitCell_nonempty
        hsub hmap w e ⟨x, hxC, hxe⟩
      exact Or.inl (mem_iUnion₂.mpr ⟨e, hwe, hxe⟩)
    · have hwt := (section34GraphVertexCell_inter_simplexBody_nonempty_iff
        hsub hmap w t.2.1).mp ⟨x, hxC, section34GraphResidualCell_subset_simplexBody t.2.1 hxi⟩
      exact Or.inr (mem_iUnion₂.mpr ⟨t, hwt, hxi, hxC⟩)
  · refine union_subset (iUnion₂_subset fun e hwe => ?_)
      (iUnion₂_subset fun t _ => ?_)
    · exact section34GraphSplitCell_subset_vertex_boundary hsub hmap hK' w e hwe
    · exact section34GraphResidualCell_inter_vertex_subset_boundary
        hsub hmap hK'.isCombinatorialManifoldWithBoundary t.1 w

theorem section34GraphVertexBoundary_eq_iUnion_proper_faces
    (hU : IsOpen U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    (hmap : 𝒦'.map = 𝒦.map) (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (w : Section34VertexIndex 𝒦 𝒦') :
    section34GraphVertexBoundary 𝒦 𝒦' w =
      ⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.vertexBall w) \ {.vertexBall w},
        section34GraphCutFamily 𝒦 𝒦' m := by
  classical
  have hC := isPLCellOn_section34GraphVertexCell hsub hmap
    hK'.isCombinatorialManifoldWithBoundary w
  apply Subset.antisymm
  · intro x hx
    rw [section34GraphVertexBoundary_eq_iUnion_splits_union_patches hU hsub hmap hK hK'] at hx
    rcases hx with hx | hx
    · obtain ⟨e, hwe, hxe⟩ := mem_iUnion₂.mp hx
      have he := (section34GraphSplitCell_subset_vertex_boundary hsub hmap hK' w e hwe).trans
        hC.boundary_subset
      exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨he, by simp⟩, hxe⟩
    · obtain ⟨t, hwt, hxt⟩ := mem_iUnion₂.mp hx
      let p : Section34PatchIndex 𝒦 𝒦' := ⟨(t, w), hwt⟩
      exact mem_iUnion₂.mpr ⟨.patch p, ⟨inter_subset_right, by simp⟩, hxt⟩
  · refine iUnion₂_subset fun l hl => ?_
    have hsubC : section34GraphCutFamily 𝒦 𝒦' l ⊆ section34GraphVertexCell 𝒦 𝒦' w := hl.1
    have hne : l ≠ .vertexBall w := hl.2
    have hR : ∀ t x, x ∈ section34GraphResidualCell 𝒦 𝒦' t →
        x ∈ section34GraphVertexCell 𝒦 𝒦' w → x ∈ section34GraphVertexBoundary 𝒦 𝒦' w :=
      fun t x hxR hxC => section34GraphResidualCell_inter_vertex_subset_boundary
        hsub hmap hK'.isCombinatorialManifoldWithBoundary t w ⟨hxR, hxC⟩
    cases l with
    | vertexBall z =>
        exact (hne (congrArg Section34Label.vertexBall
          ((section34GraphVertexCell_subset_iff z w).mp hsubC))).elim
    | splitDisk e =>
        obtain ⟨x, hx⟩ := (isPLCellOn_section34GraphSplitCell hK' e).nonempty
        have hwe := vertex_subset_edge_of_section34GraphVertexCell_inter_splitCell_nonempty
          hsub hmap w e ⟨x, hsubC hx, hx⟩
        exact section34GraphSplitCell_subset_vertex_boundary hsub hmap hK' w e hwe
    | tetraBall t => exact fun x hx => hR t.1 x hx (hsubC hx)
    | faceDisk s => exact fun x hx => hR s.1 x hx (hsubC hx)
    | patch p => exact fun x hx => hR p.1.1.1 x hx.1 (hsubC hx)
    | faceArc a => exact fun x hx => hR a.1.1.1 x hx.2 (hsubC hx)
    | edgeArc i => exact fun x hx => hR i.1.1.1 x hx.1 (hsubC hx)
    | markedPoint p => exact fun x hx => hR p.1.1.1 x hx.2 (hsubC hx)

end DifferentialGeometry.Topology.PiecewiseLinear
