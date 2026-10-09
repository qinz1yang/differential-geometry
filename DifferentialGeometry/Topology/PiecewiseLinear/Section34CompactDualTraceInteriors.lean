/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTetraBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTraceIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSplitSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem compact_vertex_subset_edge_of_mem
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (w : Section34CompactVertexIndex K K) (e : Section34CompactEdgeIndex K K) {x : E3}
    (hxV : x ∈ compactDualVertexBall M K w) (hxD : x ∈ compactDualSplitDisk M K hKM e) :
    w.1 ⊆ e.1 :=
  compact_vertex_split_incidence hKM w e (singleton_centroid_eq_compactVertexIndex w).symm
    ⟨x, hxV, hxD⟩

private theorem compact_face_eq_of_mem
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces] (hKM : K.faces ⊆ M.faces)
    (s t : Section34CompactSimplexIndex K 3) {x : E3}
    (hxs : x ∈ compactDualResidualCell M K s.1) (hxt : x ∈ compactDualResidualCell M K t.1) :
    s = t := by
  by_contra hne
  exact Set.disjoint_left.mp (disjoint_compactDualFaceDisk M K hKM s t hne) hxs hxt

private theorem compact_edge_eq_of_mem
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (e f : Section34CompactEdgeIndex K K) {x : E3}
    (hxe : x ∈ compactDualSplitDisk M K hKM e) (hxf : x ∈ compactDualSplitDisk M K hKM f) :
    e = f := by
  by_contra hne
  exact Set.disjoint_left.mp (disjoint_compactDualSplitDisk M K hKM e f hne) hxe hxf

open Classical in
theorem compactDualPatch_inter_patch_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces)
    (hstep : ∀ l m, Section34CompactCutStep l m →
      compactDualCutCell M K hKM l ⊆ compactDualCutBoundary M K hKM m)
    (p q : Section34CompactPatchIndex K K) (hpq : p ≠ q) :
    compactDualCutCell M K hKM (.patch p) ∩ compactDualCutCell M K hKM (.patch q) ⊆
      compactDualCutBoundary M K hKM (.patch p) ∪
        compactDualCutBoundary M K hKM (.patch q) := by
  intro x hx
  by_cases ht : p.1.1 = q.1.1
  · have hw : p.1.2 ≠ q.1.2 := fun h => hpq (Subtype.ext (Prod.ext ht h))
    obtain ⟨e, hxE⟩ := mem_iUnion.mp
      (compactDualVertexBall_inter_subset_splitDisks M K hKM p.1.2 q.1.2 hw
        ⟨hx.1.2, hx.2.2⟩)
    have hinc := section34Incident_of_nonempty_compactDualSplitDisk_inter_residual
      M K hKM e p.1.1.2.1 ⟨x, hxE, hx.1.1⟩
    let i : Section34CompactEdgeArcIndex K K := ⟨(p.1.1, e), hinc⟩
    have hwe := compact_vertex_subset_edge_of_mem M K hKM p.1.2 e hx.1.2 hxE
    exact Or.inl (hstep (.edgeArc i) (.patch p) ⟨rfl, hwe⟩ ⟨hx.1.1, hxE⟩)
  · obtain ⟨s, hs, -, hxS⟩ := exists_compact_faceDisk_of_tetra_inter M K hKM
      p.1.1 q.1.1 ht ⟨hx.1.1, hx.2.1⟩
    have hinc := section34Incident_of_nonempty_compactDualVertexBall_inter_faceDisk
      M K hKM p.1.2 s ⟨x, hx.1.2, hxS⟩
    let a : Section34CompactArcIndex K K := ⟨(s, p.1.2), hinc⟩
    exact Or.inl (hstep (.faceArc a) (.patch p) ⟨rfl, hs⟩ ⟨hx.1.2, hxS⟩)

open Classical in
theorem compactDualPatch_inter_faceArc_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces)
    (hstep : ∀ l m, Section34CompactCutStep l m →
      compactDualCutCell M K hKM l ⊆ compactDualCutBoundary M K hKM m)
    (p : Section34CompactPatchIndex K K) (a : Section34CompactArcIndex K K) :
    compactDualCutCell M K hKM (.patch p) ∩ compactDualCutCell M K hKM (.faceArc a) ⊆
      compactDualCutBoundary M K hKM (.patch p) ∪
        compactDualCutBoundary M K hKM (.faceArc a) := by
  intro x hx
  by_cases hw : p.1.2 = a.1.2
  · have hinc := section34Incident_of_nonempty_compactDualFaceDisk_inter_residual
      M K hKM a.1.1 p.1.1.2.1 ⟨x, hx.2.2, hx.1.1⟩
    exact Or.inl (hstep (.faceArc a) (.patch p) ⟨hw.symm, hinc⟩ hx.2)
  · obtain ⟨e, hxE⟩ := mem_iUnion.mp
      (compactDualVertexBall_inter_subset_splitDisks M K hKM p.1.2 a.1.2 hw
        ⟨hx.1.2, hx.2.1⟩)
    have hinc := section34Incident_of_nonempty_compactDualSplitDisk_inter_residual
      M K hKM e a.1.1.2.1 ⟨x, hxE, hx.2.2⟩
    let q : Section34CompactMarkIndex K K := ⟨(a.1.1, e), hinc⟩
    have hwe := compact_vertex_subset_edge_of_mem M K hKM a.1.2 e hx.2.1 hxE
    exact Or.inr (hstep (.markedPoint q) (.faceArc a) ⟨rfl, hwe⟩ ⟨hxE, hx.2.2⟩)

open Classical in
theorem compactDualPatch_inter_edgeArc_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces)
    (hstep : ∀ l m, Section34CompactCutStep l m →
      compactDualCutCell M K hKM l ⊆ compactDualCutBoundary M K hKM m)
    (p : Section34CompactPatchIndex K K) (i : Section34CompactEdgeArcIndex K K) :
    compactDualCutCell M K hKM (.patch p) ∩ compactDualCutCell M K hKM (.edgeArc i) ⊆
      compactDualCutBoundary M K hKM (.patch p) ∪
        compactDualCutBoundary M K hKM (.edgeArc i) := by
  intro x hx
  by_cases ht : p.1.1 = i.1.1
  · have hwe := compact_vertex_subset_edge_of_mem M K hKM p.1.2 i.1.2 hx.1.2 hx.2.2
    exact Or.inl (hstep (.edgeArc i) (.patch p) ⟨ht.symm, hwe⟩ hx.2)
  · obtain ⟨s, -, hs, hxS⟩ := exists_compact_faceDisk_of_tetra_inter M K hKM
      p.1.1 i.1.1 ht ⟨hx.1.1, hx.2.1⟩
    have hinc := section34Incident_of_nonempty_compactDualSplitDisk_inter_residual
      M K hKM i.1.2 s.2.1 ⟨x, hx.2.2, hxS⟩
    let q : Section34CompactMarkIndex K K := ⟨(s, i.1.2), hinc⟩
    exact Or.inr (hstep (.markedPoint q) (.edgeArc i) ⟨rfl, hs⟩ ⟨hx.2.2, hxS⟩)

open Classical in
theorem compactDualPatch_inter_markedPoint_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces)
    (hstep : ∀ l m, Section34CompactCutStep l m →
      compactDualCutCell M K hKM l ⊆ compactDualCutBoundary M K hKM m)
    (p : Section34CompactPatchIndex K K) (q : Section34CompactMarkIndex K K) :
    compactDualCutCell M K hKM (.patch p) ∩ compactDualCutCell M K hKM (.markedPoint q) ⊆
      compactDualCutBoundary M K hKM (.patch p) ∪
        compactDualCutBoundary M K hKM (.markedPoint q) := by
  intro x hx
  have hinc := section34Incident_of_nonempty_compactDualSplitDisk_inter_residual
    M K hKM q.1.2 p.1.1.2.1 ⟨x, hx.2.1, hx.1.1⟩
  let i : Section34CompactEdgeArcIndex K K := ⟨(p.1.1, q.1.2), hinc⟩
  have hwe := compact_vertex_subset_edge_of_mem M K hKM p.1.2 q.1.2 hx.1.2 hx.2.1
  exact Or.inl (hstep (.edgeArc i) (.patch p) ⟨rfl, hwe⟩ ⟨hx.1.1, hx.2.1⟩)

open Classical in
theorem compactDualFaceArc_inter_faceArc_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces)
    (hstep : ∀ l m, Section34CompactCutStep l m →
      compactDualCutCell M K hKM l ⊆ compactDualCutBoundary M K hKM m)
    (a b : Section34CompactArcIndex K K) (hab : a ≠ b) :
    compactDualCutCell M K hKM (.faceArc a) ∩ compactDualCutCell M K hKM (.faceArc b) ⊆
      compactDualCutBoundary M K hKM (.faceArc a) ∪
        compactDualCutBoundary M K hKM (.faceArc b) := by
  intro x hx
  have hs := compact_face_eq_of_mem M K hKM a.1.1 b.1.1 hx.1.2 hx.2.2
  have hw : a.1.2 ≠ b.1.2 := fun h => hab (Subtype.ext (Prod.ext hs h))
  obtain ⟨e, hxE⟩ := mem_iUnion.mp
    (compactDualVertexBall_inter_subset_splitDisks M K hKM a.1.2 b.1.2 hw
      ⟨hx.1.1, hx.2.1⟩)
  have hinc := section34Incident_of_nonempty_compactDualSplitDisk_inter_residual
    M K hKM e a.1.1.2.1 ⟨x, hxE, hx.1.2⟩
  let p : Section34CompactMarkIndex K K := ⟨(a.1.1, e), hinc⟩
  have hwe := compact_vertex_subset_edge_of_mem M K hKM a.1.2 e hx.1.1 hxE
  exact Or.inl (hstep (.markedPoint p) (.faceArc a) ⟨rfl, hwe⟩ ⟨hxE, hx.1.2⟩)

open Classical in
theorem compactDualFaceArc_inter_edgeArc_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3)
    (hKM : K.faces ⊆ M.faces)
    (hstep : ∀ l m, Section34CompactCutStep l m →
      compactDualCutCell M K hKM l ⊆ compactDualCutBoundary M K hKM m)
    (a : Section34CompactArcIndex K K) (i : Section34CompactEdgeArcIndex K K) :
    compactDualCutCell M K hKM (.faceArc a) ∩ compactDualCutCell M K hKM (.edgeArc i) ⊆
      compactDualCutBoundary M K hKM (.faceArc a) ∪
        compactDualCutBoundary M K hKM (.edgeArc i) := by
  intro x hx
  have hinc := section34Incident_of_nonempty_compactDualSplitDisk_inter_residual
    M K hKM i.1.2 a.1.1.2.1 ⟨x, hx.2.2, hx.1.2⟩
  let p : Section34CompactMarkIndex K K := ⟨(a.1.1, i.1.2), hinc⟩
  have hwe := compact_vertex_subset_edge_of_mem M K hKM a.1.2 i.1.2 hx.1.1 hx.2.2
  exact Or.inl (hstep (.markedPoint p) (.faceArc a) ⟨rfl, hwe⟩ ⟨hx.2.2, hx.1.2⟩)

open Classical in
theorem compactDualFaceArc_inter_markedPoint_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces)
    (hstep : ∀ l m, Section34CompactCutStep l m →
      compactDualCutCell M K hKM l ⊆ compactDualCutBoundary M K hKM m)
    (a : Section34CompactArcIndex K K) (p : Section34CompactMarkIndex K K) :
    compactDualCutCell M K hKM (.faceArc a) ∩ compactDualCutCell M K hKM (.markedPoint p) ⊆
      compactDualCutBoundary M K hKM (.faceArc a) ∪
        compactDualCutBoundary M K hKM (.markedPoint p) := by
  intro x hx
  have hs := compact_face_eq_of_mem M K hKM p.1.1 a.1.1 hx.2.2 hx.1.2
  have hwe := compact_vertex_subset_edge_of_mem M K hKM a.1.2 p.1.2 hx.1.1 hx.2.1
  exact Or.inl (hstep (.markedPoint p) (.faceArc a) ⟨hs, hwe⟩ hx.2)

open Classical in
theorem compactDualEdgeArc_inter_edgeArc_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces)
    (hstep : ∀ l m, Section34CompactCutStep l m →
      compactDualCutCell M K hKM l ⊆ compactDualCutBoundary M K hKM m)
    (i j : Section34CompactEdgeArcIndex K K) (hij : i ≠ j) :
    compactDualCutCell M K hKM (.edgeArc i) ∩ compactDualCutCell M K hKM (.edgeArc j) ⊆
      compactDualCutBoundary M K hKM (.edgeArc i) ∪
        compactDualCutBoundary M K hKM (.edgeArc j) := by
  intro x hx
  have he := compact_edge_eq_of_mem M K hKM i.1.2 j.1.2 hx.1.2 hx.2.2
  have ht : i.1.1 ≠ j.1.1 := fun h => hij (Subtype.ext (Prod.ext h he))
  obtain ⟨s, hs, -, hxS⟩ := exists_compact_faceDisk_of_tetra_inter M K hKM
    i.1.1 j.1.1 ht ⟨hx.1.1, hx.2.1⟩
  have hinc := section34Incident_of_nonempty_compactDualSplitDisk_inter_residual
    M K hKM i.1.2 s.2.1 ⟨x, hx.1.2, hxS⟩
  let p : Section34CompactMarkIndex K K := ⟨(s, i.1.2), hinc⟩
  exact Or.inl (hstep (.markedPoint p) (.edgeArc i) ⟨rfl, hs⟩ ⟨hx.1.2, hxS⟩)

open Classical in
theorem compactDualEdgeArc_inter_markedPoint_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces)
    (hstep : ∀ l m, Section34CompactCutStep l m →
      compactDualCutCell M K hKM l ⊆ compactDualCutBoundary M K hKM m)
    (i : Section34CompactEdgeArcIndex K K) (p : Section34CompactMarkIndex K K) :
    compactDualCutCell M K hKM (.edgeArc i) ∩ compactDualCutCell M K hKM (.markedPoint p) ⊆
      compactDualCutBoundary M K hKM (.edgeArc i) ∪
        compactDualCutBoundary M K hKM (.markedPoint p) := by
  intro x hx
  have he := compact_edge_eq_of_mem M K hKM p.1.2 i.1.2 hx.2.1 hx.1.2
  have hinc := section34Incident_of_nonempty_compactDualFaceDisk_inter_residual
    M K hKM p.1.1 i.1.1.2.1 ⟨x, hx.2.2, hx.1.1⟩
  exact Or.inl (hstep (.markedPoint p) (.edgeArc i) ⟨he, hinc⟩ hx.2)

open Classical in
theorem compactDualMarkedPoint_inter_markedPoint_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces] (hKM : K.faces ⊆ M.faces)
    (p q : Section34CompactMarkIndex K K) (hpq : p ≠ q) :
    compactDualCutCell M K hKM (.markedPoint p) ∩ compactDualCutCell M K hKM (.markedPoint q) ⊆
      compactDualCutBoundary M K hKM (.markedPoint p) ∪
        compactDualCutBoundary M K hKM (.markedPoint q) := by
  intro x hx
  have hs := compact_face_eq_of_mem M K hKM p.1.1 q.1.1 hx.1.2 hx.2.2
  have he := compact_edge_eq_of_mem M K hKM p.1.2 q.1.2 hx.1.1 hx.2.1
  exact (hpq (Subtype.ext (Prod.ext hs he))).elim

end DifferentialGeometry.Topology.PiecewiseLinear
