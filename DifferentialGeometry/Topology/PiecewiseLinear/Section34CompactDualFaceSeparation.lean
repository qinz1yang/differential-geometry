/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedIntervalLink
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCellSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTopInteriors
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTriangleBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualFaceDisk_subset_openSimplex
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s : Section34CompactSimplexIndex K 3) :
    compactDualResidualCell M K s.1 ⊆ openSimplex s.1 := by
  let S := restrict M (convexHull ℝ (s.1 : Set E3))
  let A := simplexBoundary s.1 (M.indep (hKM s.2.1))
  have hsS : s.1 ∈ S.faces := ⟨hKM s.2.1, subset_rfl⟩
  have hAS : A.faces ⊆ S.faces := by
    intro r hr
    exact ⟨M.down_closed (hKM s.2.1) hr.1 hr.2.1,
      convexHull_mono (Finset.coe_subset.mpr hr.1)⟩
  have hsA : s.1 ∉ A.faces := fun h => h.2.2 rfl
  have hdis := derivedNeighborhoodCell_disjoint_subcomplex_of_not_mem S A hAS hsS hsA
  rw [compactDualResidualCell_eq_derived_triangle M K hKM s]
  intro x hx
  rw [openSimplex_eq_sdiff_simplexBoundary s.1 (M.indep (hKM s.2.1))]
  have hxS : x ∈ S.space := derivedNeighborhoodCell_space_subset S s.1 hx
  have hspace : S.space = convexHull ℝ (s.1 : Set E3) :=
    restrict_convexHull_space (hKM s.2.1)
  exact ⟨hspace ▸ hxS, fun hxA => Set.disjoint_left.mp hdis hx hxA⟩

open Classical in
theorem disjoint_compactDualFaceDisk
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s t : Section34CompactSimplexIndex K 3) (hst : s ≠ t) :
    Disjoint (compactDualResidualCell M K s.1) (compactDualResidualCell M K t.1) := by
  apply Set.disjoint_left.mpr
  intro x hxs hxt
  have hxS := compactDualFaceDisk_subset_openSimplex M K hKM s hxs
  have hxT := compactDualFaceDisk_subset_openSimplex M K hKM t hxt
  have hst' := face_subset_of_mem_openSimplex_of_mem_convexHull K s.2.1 t.2.1 hxS
    (openSimplex_subset_convexHull _ hxT)
  exact hst (Subtype.ext (Finset.eq_of_subset_of_card_le hst' (by rw [s.2.2, t.2.2])))

open Classical in
theorem compactDualFaceDisk_inter_neighborhood_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s : Section34CompactSimplexIndex K 3) :
    compactDualResidualCell M K s.1 ∩ compactDualNeighborhood M K ⊆
      compactDualCutBoundary M K hKM (.faceDisk s) := by
  rintro x ⟨hxF, hxN⟩
  obtain ⟨v, hv, hxV⟩ := mem_iUnion₂.mp hxN
  have hxS : x ∈ convexHull ℝ (s.1 : Set E3) :=
    openSimplex_subset_convexHull _ (compactDualFaceDisk_subset_openSimplex M K hKM s hxF)
  have hvs : v ∈ s.1 := by
    by_contra hvs
    have hzero := graphDualCell_space_inter_convexHull_eq_empty
      (restrict K (section34CompactGraphSkeleton K)) (hKM hv) (hKM s.2.1) hvs
    exact (eq_empty_iff_forall_notMem.mp hzero) x ⟨hxV, hxS⟩
  let w : Section34CompactVertexIndex K K := ⟨{v}, hv, Finset.card_singleton v,
    convexHull_subset_section34CompactGraphSkeleton hv (by simp)⟩
  have hinc : Section34Incident w.1 s.1 := by
    intro y hy
    have hyv : y = v := Finset.mem_singleton.mp hy
    subst y
    exact subset_convexHull ℝ _ hvs
  let a : Section34CompactArcIndex K K := ⟨(s, w), hinc⟩
  rw [compactDualCutBoundary_faceDisk_eq_iUnion_faceArc M K hKM s]
  refine mem_iUnion₂.mpr ⟨a, rfl, ?_⟩
  change x ∈ compactDualVertexBall M K w ∩ compactDualResidualCell M K s.1
  refine ⟨?_, hxF⟩
  simpa only [compactDualVertexBall, w, Finset.centroid_singleton, id_eq] using hxV

theorem compactDualFaceDisk_inter_cell_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (s : Section34CompactSimplexIndex K 3)
    (l : Section34CompactLabelOf K K) (hl : section34BoundedDim l ≤ 2)
    (hne : .faceDisk s ≠ l) :
    compactDualResidualCell M K s.1 ∩ compactDualCutCell M K hKM l ⊆
      compactDualCutBoundary M K hKM (.faceDisk s) := by
  have hN := compactDualFaceDisk_inter_neighborhood_subset_boundary M K hKM s
  cases l with
  | vertexBall w => simp [section34BoundedDim] at hl
  | tetraBall t => simp [section34BoundedDim] at hl
  | splitDisk e =>
    exact (inter_subset_inter_right _
      (compactDualSplitDisk_subset_neighborhood M K hKM e)).trans hN
  | faceDisk t =>
    intro x hx
    exact (Set.disjoint_left.mp (disjoint_compactDualFaceDisk M K hKM s t
      (fun h => hne (congrArg Section34BoundedLabel.faceDisk h))) hx.1 hx.2).elim
  | patch p =>
    intro x hx
    exact hN ⟨hx.1, compactDualVertexBall_subset_neighborhood M K p.1.2 hx.2.2⟩
  | faceArc a =>
    intro x hx
    exact hN ⟨hx.1, compactDualVertexBall_subset_neighborhood M K a.1.2 hx.2.1⟩
  | edgeArc i =>
    intro x hx
    exact hN ⟨hx.1, compactDualSplitDisk_subset_neighborhood M K hKM i.1.2 hx.2.2⟩
  | markedPoint p =>
    intro x hx
    exact hN ⟨hx.1, compactDualSplitDisk_subset_neighborhood M K hKM p.1.2 hx.2.1⟩
  | outerFace o =>
    intro x hx
    exact hN ⟨hx.1, compactDualVertexBall_subset_neighborhood M K o.1
      (compactDualOuterFace_subset_vertexBall M K hKM o hx.2)⟩
  | outerArc q =>
    intro x hx
    exact hN ⟨hx.1, compactDualSplitDisk_subset_neighborhood M K hKM q.1
      (compactDualOuterArc_subset_splitDisk M K hKM q hx.2)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
