/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualEdgeEndpoints
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTriangleEndpoints
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactIncidentEdges

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem compact_subset_of_incident (K : Geometry.SimplicialComplex ℝ E3)
    {s t : Finset E3} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (h : Section34Incident s t) : s ⊆ t := by
  intro v hv
  have hvK := K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)
  exact mem_of_mem_convexHull_of_singleton_mem K hvK ht (h hv)

open Classical in
private theorem compact_edge_other_vertex (e : Finset E3) (hc : e.card = 2)
    {v : E3} (hv : v ∈ e) : ∃ u, v ≠ u ∧ e = {v, u} := by
  obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne (by omega : 1 < e.card) v
  have hsub : ({v, u} : Finset E3) ⊆ e :=
    Finset.insert_subset_iff.mpr ⟨hv, Finset.singleton_subset_iff.mpr hu⟩
  have heq : ({v, u} : Finset E3) = e :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair huv.symm, hc])
  exact ⟨u, huv.symm, heq.symm⟩

open Classical in
private theorem compact_triangles_at_edge (K : Geometry.SimplicialComplex ℝ E3)
    (i : Section34CompactEdgeArcIndex K K) :
    ∃ s f : Section34CompactSimplexIndex K 3, s ≠ f ∧
      Section34Incident i.1.2.1 s.1 ∧ Section34Incident i.1.2.1 f.1 ∧
      Section34Incident s.1 i.1.1.1 ∧ Section34Incident f.1 i.1.1.1 ∧
      ∀ g : Section34CompactSimplexIndex K 3,
        Section34Incident i.1.2.1 g.1 → Section34Incident g.1 i.1.1.1 → g = s ∨ g = f := by
  let t := i.1.1
  let e := i.1.2
  have het : e.1 ⊆ t.1 := compact_subset_of_incident K e.2.1 t.2.1 i.2
  have hc : (t.1 \ e.1).card = 2 := by
    rw [Finset.card_sdiff_of_subset het, t.2.2, e.2.2.1]
  obtain ⟨u, v, huv, hrest⟩ := Finset.card_eq_two.mp hc
  have hu : u ∈ t.1 \ e.1 := by rw [hrest]; simp
  have hv : v ∈ t.1 \ e.1 := by rw [hrest]; simp
  have hut := (Finset.mem_sdiff.mp hu).1
  have hue := (Finset.mem_sdiff.mp hu).2
  have hvt := (Finset.mem_sdiff.mp hv).1
  have hve := (Finset.mem_sdiff.mp hv).2
  have hsu : insert u e.1 ⊆ t.1 := Finset.insert_subset_iff.mpr ⟨hut, het⟩
  have hfv : insert v e.1 ⊆ t.1 := Finset.insert_subset_iff.mpr ⟨hvt, het⟩
  have hsc : (insert u e.1).card = 3 := by rw [Finset.card_insert_of_notMem hue, e.2.2.1]
  have hfc : (insert v e.1).card = 3 := by rw [Finset.card_insert_of_notMem hve, e.2.2.1]
  let s : Section34CompactSimplexIndex K 3 :=
    ⟨insert u e.1, K.down_closed t.2.1 hsu (Finset.insert_nonempty _ _), hsc⟩
  let f : Section34CompactSimplexIndex K 3 :=
    ⟨insert v e.1, K.down_closed t.2.1 hfv (Finset.insert_nonempty _ _), hfc⟩
  have hsf : s ≠ f := by
    intro h
    have hval : insert u e.1 = insert v e.1 := congrArg Subtype.val h
    have humem : u ∈ insert v e.1 := hval ▸ Finset.mem_insert_self u e.1
    rcases Finset.mem_insert.mp humem with huv' | hue'
    · exact huv huv'
    · exact hue hue'
  have hinc {a b : Finset E3} (hab : a ⊆ b) : Section34Incident a b :=
    (Finset.coe_subset.mpr hab).trans (subset_convexHull ℝ _)
  refine ⟨s, f, hsf, hinc (Finset.subset_insert _ _), hinc (Finset.subset_insert _ _),
    hinc hsu, hinc hfv, ?_⟩
  intro g heg hgt
  have heg' : e.1 ⊆ g.1 := compact_subset_of_incident K e.2.1 g.2.1 heg
  have hgt' : g.1 ⊆ t.1 := compact_subset_of_incident K g.2.1 t.2.1 hgt
  have hgc : (g.1 \ e.1).card = 1 := by
    rw [Finset.card_sdiff_of_subset heg', g.2.2, e.2.2.1]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hgc
  have hzg : z ∈ g.1 \ e.1 := by rw [hz]; exact Finset.mem_singleton_self z
  have hzg' := (Finset.mem_sdiff.mp hzg).1
  have hze := (Finset.mem_sdiff.mp hzg).2
  have hzt : z ∈ t.1 \ e.1 := Finset.mem_sdiff.mpr ⟨hgt' hzg', hze⟩
  have hgeq : insert z e.1 = g.1 := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset_iff.mpr ⟨hzg', heg'⟩)
    (by rw [Finset.card_insert_of_notMem hze, e.2.2.1, g.2.2])
  rw [hrest] at hzt
  rcases Finset.mem_insert.mp hzt with hzu | hzv
  · left
    apply Subtype.ext
    change g.1 = insert u e.1
    rw [← hgeq, hzu]
  · right
    apply Subtype.ext
    change g.1 = insert v e.1
    rw [← hgeq, Finset.mem_singleton.mp hzv]

open Classical in
theorem compactDualCutBoundary_faceArc_eq_iUnion_markedPoint
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (a : Section34CompactArcIndex K K) :
    compactDualCutBoundary M K hKM (.faceArc a) =
      ⋃ (p : Section34CompactMarkIndex K K)
        (_ : Section34CompactCutStep (.markedPoint p) (.faceArc a)),
          compactDualCutCell M K hKM (.markedPoint p) := by
  obtain ⟨e, f, hef, hes, hfs, hwe, hwf, hall⟩ :=
    exists_section34CompactEdgeIndex_pair_of_incident (IsSubdivision.refl K)
      ((Set.toFinite M.faces).subset hKM) a.1.1 a.1.2 a.2
  let v := a.1.2.1.centroid ℝ id
  have hvw : v ∈ a.1.2.1 := by
    rw [← singleton_centroid_eq_compactVertexIndex a.1.2]
    exact Finset.mem_singleton_self _
  obtain ⟨u, hvu, heu⟩ := compact_edge_other_vertex e.1 e.2.2.1 (hwe hvw)
  obtain ⟨z, hvz, hfz⟩ := compact_edge_other_vertex f.1 f.2.2.1 (hwf hvw)
  have hus : u ∈ a.1.1.1 :=
    compact_subset_of_incident K e.2.1 a.1.1.2.1 hes (by rw [heu]; simp)
  have hzs : z ∈ a.1.1.1 :=
    compact_subset_of_incident K f.2.1 a.1.1.2.1 hfs (by rw [hfz]; simp)
  have huz : u ≠ z := by
    intro h
    apply hef
    apply Subtype.ext
    rw [heu, hfz, h]
  let p : Section34CompactMarkIndex K K := ⟨(a.1.1, e), hes⟩
  let q : Section34CompactMarkIndex K K := ⟨(a.1.1, f), hfs⟩
  have hpstep : Section34CompactCutStep (.markedPoint p) (.faceArc a) := ⟨rfl, hwe⟩
  have hqstep : Section34CompactCutStep (.markedPoint q) (.faceArc a) := ⟨rfl, hwf⟩
  have hbd : compactDualCutBoundary M K hKM (.faceArc a) =
      compactDualCutCell M K hKM (.markedPoint p) ∪
        compactDualCutCell M K hKM (.markedPoint q) := by
    rw [compactDualCutBoundary_faceArc_eq_pair M K hKM a hus hzs hvu hvz huz,
      compactDualCutCell_markedPoint_eq_singleton M K hKM p,
      compactDualCutCell_markedPoint_eq_singleton M K hKM q]
    simp only [p, q, heu, hfz, v]
    ext x
    simp only [mem_insert_iff, mem_singleton_iff, mem_union]
  rw [hbd]
  apply Subset.antisymm
  · exact union_subset (subset_iUnion₂_of_subset p hpstep subset_rfl)
      (subset_iUnion₂_of_subset q hqstep subset_rfl)
  · refine iUnion₂_subset fun r hr => ?_
    change r.1.1 = a.1.1 ∧ a.1.2.1 ⊆ r.1.2.1 at hr
    have hin : Section34Incident r.1.2.1 a.1.1.1 := by simpa only [hr.1] using r.2
    rcases hall r.1.2 hin hr.2 with he | hf
    · have hrp : r = p := Subtype.ext (Prod.ext hr.1 he)
      rw [hrp]
      exact subset_union_left
    · have hrq : r = q := Subtype.ext (Prod.ext hr.1 hf)
      rw [hrq]
      exact subset_union_right

open Classical in
theorem compactDualCutBoundary_edgeArc_eq_iUnion_markedPoint
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (i : Section34CompactEdgeArcIndex K K) :
    compactDualCutBoundary M K hKM (.edgeArc i) =
      ⋃ (p : Section34CompactMarkIndex K K)
        (_ : Section34CompactCutStep (.markedPoint p) (.edgeArc i)),
          compactDualCutCell M K hKM (.markedPoint p) := by
  obtain ⟨s, f, hsf, hes, hef, hst, hft, hall⟩ := compact_triangles_at_edge K i
  let p : Section34CompactMarkIndex K K := ⟨(s, i.1.2), hes⟩
  let q : Section34CompactMarkIndex K K := ⟨(f, i.1.2), hef⟩
  have hpstep : Section34CompactCutStep (.markedPoint p) (.edgeArc i) := ⟨rfl, hst⟩
  have hqstep : Section34CompactCutStep (.markedPoint q) (.edgeArc i) := ⟨rfl, hft⟩
  have hbd : compactDualCutBoundary M K hKM (.edgeArc i) =
      compactDualCutCell M K hKM (.markedPoint p) ∪
        compactDualCutCell M K hKM (.markedPoint q) := by
    rw [compactDualCutBoundary_edgeArc_eq_pair M K hKM i s f hes hef hst hft hsf,
      compactDualCutCell_markedPoint_eq_singleton M K hKM p,
      compactDualCutCell_markedPoint_eq_singleton M K hKM q]
    ext x
    simp only [p, q, mem_insert_iff, mem_singleton_iff, mem_union]
  rw [hbd]
  apply Subset.antisymm
  · exact union_subset (subset_iUnion₂_of_subset p hpstep subset_rfl)
      (subset_iUnion₂_of_subset q hqstep subset_rfl)
  · refine iUnion₂_subset fun r hr => ?_
    change r.1.2 = i.1.2 ∧ Section34Incident r.1.1.1 i.1.1.1 at hr
    have hin : Section34Incident i.1.2.1 r.1.1.1 := by simpa only [hr.1] using r.2
    rcases hall r.1.1 hin hr.2 with hs | hf
    · have hrp : r = p := Subtype.ext (Prod.ext hs hr.1)
      rw [hrp]
      exact subset_union_left
    · have hrq : r = q := Subtype.ext (Prod.ext hf hr.1)
      rw [hrq]
      exact subset_union_right

end DifferentialGeometry.Topology.PiecewiseLinear
