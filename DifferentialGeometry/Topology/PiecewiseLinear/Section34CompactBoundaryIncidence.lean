/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTetraIncidence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

private theorem source_subset_boundary_of_ne
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m l : Section34CompactLabelOf K K'} (hml : src m ⊆ src l) (hne : m ≠ l) :
    src m ⊆ srcBd l := by
  obtain ⟨-, -, -, -, -, -, -, hbd, -⟩ := hcut
  rw [hbd l]
  exact subset_iUnion₂_of_subset m ⟨hml, hne⟩ subset_rfl

theorem Section34CompactCutFrame.tetra_eq_of_boundary_triangle
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (s : Section34CompactSimplexIndex K 3)
    (hs : convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space)
    {t u : Section34CompactSimplexIndex K 4}
    (hst : Section34Incident s.1 t.1) (hsu : Section34Incident s.1 u.1) : t = u := by
  classical
  let _ : DecidableEq E3 := Classical.decEq E3
  obtain ⟨-, hK, -, hman, -⟩ := hcut
  let _ : Finite K.faces := hK.to_subtype
  have hfront := frontier_space_eq_boundaryComplex_space (n := 2) hman
  have hsBd : s.1 ∈ (boundaryComplex 3 K).faces := by
    apply mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 K) s.2.1
      (centroid_mem_openSimplex (K.nonempty_of_mem_faces s.2.1))
    rw [← hfront]
    exact hs (s.1.centroid_mem_convexHull (K.nonempty_of_mem_faces s.2.1))
  obtain ⟨v, hv⟩ := (hman.mem_boundaryComplex_iff_unique_coface K s.2.2).mp hsBd
  have huniq (a : Section34CompactSimplexIndex K 4) (hsa : Section34Incident s.1 a.1) :
      a.1 = insert v s.1 := by
    have hsub : s.1 ⊆ a.1 := face_subset_of_mem_openSimplex_of_mem_convexHull K s.2.1 a.2.1
      (centroid_mem_openSimplex (K.nonempty_of_mem_faces s.2.1))
      (convexHull_min hsa (convex_convexHull ℝ _)
        (s.1.centroid_mem_convexHull (K.nonempty_of_mem_faces s.2.1)))
    obtain ⟨w, hws, hwa⟩ := Finset.exists_eq_insert_iff.mpr
      ⟨hsub, by rw [s.2.2, a.2.2]⟩
    have hw : w ∈ {x | x ∉ s.1 ∧ insert x s.1 ∈ K.faces} :=
      ⟨hws, hwa.symm ▸ a.2.1⟩
    have hwv : w = v := hv.subset hw
    rw [← hwa, hwv]
  exact Subtype.ext ((huniq t hst).trans (huniq u hsu).symm)

theorem Section34CompactCutFrame.exists_tetra_pair_of_not_boundary_triangle
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (s : Section34CompactSimplexIndex K 3)
    (hs : ¬ convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space) :
    ∃ t u : Section34CompactSimplexIndex K 4, t ≠ u ∧
      Section34Incident s.1 t.1 ∧ Section34Incident s.1 u.1 := by
  classical
  let _ : DecidableEq E3 := Classical.decEq E3
  obtain ⟨-, hK, -, hman, -⟩ := hcut
  let _ : Finite K.faces := hK.to_subtype
  have hsBd : s.1 ∉ (boundaryComplex 3 K).faces := by
    intro h
    apply hs
    rw [frontier_space_eq_boundaryComplex_space (n := 2) hman]
    exact (boundaryComplex 3 K).convexHull_subset_space h
  obtain ⟨v, w, hvw, hpair⟩ :=
    hman.codimension_one_cofaces_of_notMem_boundary K s.2.1 s.2.2 hsBd
  have hv : v ∉ s.1 ∧ insert v s.1 ∈ K.faces :=
    hpair.symm.subset (mem_insert v {w})
  have hw : w ∉ s.1 ∧ insert w s.1 ∈ K.faces :=
    hpair.symm.subset (mem_insert_of_mem v (mem_singleton w))
  let t : Section34CompactSimplexIndex K 4 :=
    ⟨insert v s.1, hv.2, by rw [Finset.card_insert_of_notMem hv.1, s.2.2]⟩
  let u : Section34CompactSimplexIndex K 4 :=
    ⟨insert w s.1, hw.2, by rw [Finset.card_insert_of_notMem hw.1, s.2.2]⟩
  refine ⟨t, u, ?_, ?_, ?_⟩
  · intro htu
    have hvu : v ∈ insert w s.1 := by
      change v ∈ u.1
      rw [← htu]
      exact Finset.mem_insert_self v s.1
    exact hvw ((Finset.mem_insert.mp hvu).resolve_right hv.1)
  · exact (Finset.coe_subset.mpr (Finset.subset_insert v s.1)).trans (subset_convexHull ℝ _)
  · exact (Finset.coe_subset.mpr (Finset.subset_insert w s.1)).trans (subset_convexHull ℝ _)

theorem Section34CompactCutFrame.faceArc_subset_outerFace_iff
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (a : Section34CompactArcIndex K K') (o : Section34CompactOuterVertexIndex K K') :
    src (.faceArc a) ⊆ src (.outerFace o) ↔ a.1.2 = o.1 ∧
      convexHull ℝ (a.1.1.1 : Set E3) ⊆ frontier K.space := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, harc, -, hpatch, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hex⟩ := id hcut
  have hAV : src (.faceArc a) ⊆ src (.vertexBall a.1.2) := by
    rw [harc a]
    exact inter_subset_left
  have hABd := source_subset_boundary_of_ne hcut hAV (by simp)
  let p (t : Section34CompactSimplexIndex K 4) (ht : Section34Incident a.1.1.1 t.1) :
      Section34CompactPatchIndex K K' :=
    ⟨(t, a.1.2), a.2.trans (convexHull_min ht (convex_convexHull ℝ _))⟩
  have hpV (t : Section34CompactSimplexIndex K 4) (ht : Section34Incident a.1.1.1 t.1) :
      src (.patch (p t ht)) ⊆ src (.vertexBall a.1.2) := by
    rw [hpatch (p t ht)]
    exact inter_subset_right
  have hAp (t : Section34CompactSimplexIndex K 4) (ht : Section34Incident a.1.1.1 t.1) :
      src (.faceArc a) ⊆ src (.patch (p t ht)) := by
    rw [hpatch (p t ht)]
    exact subset_inter ((hcut.faceArc_subset_tetraBall_iff a t).2 ht) hAV
  have hpBd (t : Section34CompactSimplexIndex K 4) (ht : Section34Incident a.1.1.1 t.1) :
      src (.patch (p t ht)) ⊆ srcBd (.vertexBall a.1.2) :=
    source_subset_boundary_of_ne hcut (hpV t ht) (by simp)
  have hoV := (hcut.outerFace_subset_vertexBall_iff o o.1).2 rfl
  constructor
  · intro hAO
    have hwo := hcut.faceArc_eq_of_subset_vertexBall a o.1 (hAO.trans hoV)
    refine ⟨hwo, ?_⟩
    by_contra hs
    obtain ⟨t, u, htu, ht, hu⟩ := hcut.exists_tetra_pair_of_not_boundary_triangle a.1.1 hs
    have hoV' : src (.outerFace o) ⊆ src (.vertexBall a.1.2) := by
      rw [hwo]
      exact hoV
    have hoBd := source_subset_boundary_of_ne hcut hoV' (by simp)
    obtain ⟨f, g, -, -, -, -, -, -, -, hall⟩ :=
      CompactSourceFaceProbe.vertex_ball_boundary_thin hcut a.1.2 (.faceArc a) rfl hABd
    have hA := hall (.patch (p t ht)) rfl (hAp t ht) (hpBd t ht)
    have hB := hall (.patch (p u hu)) rfl (hAp u hu) (hpBd u hu)
    have hO := hall (.outerFace o) rfl hAO hoBd
    have hne : (.patch (p t ht) : Section34CompactLabelOf K K') ≠ .patch (p u hu) := by
      intro h
      exact htu (congrArg (fun x : Section34CompactPatchIndex K K' => x.1.1)
        (Section34BoundedLabel.patch.inj h))
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> rcases hO with hO | hO
    all_goals first
      | exact hne (hA.trans hB.symm)
      | cases hA.trans hO.symm
      | cases hB.trans hO.symm
  · rintro ⟨hwo, hs⟩
    obtain ⟨t, ht⟩ := hex a.1.1
    obtain ⟨f, g, hfg, hdf, hdg, hAf, hf, hAg, hg, hall⟩ :=
      CompactSourceFaceProbe.vertex_ball_boundary_thin hcut a.1.2 (.faceArc a) rfl hABd
    obtain ⟨c, hcP, hdc, hAc, hcBd⟩ : ∃ c : Section34CompactLabelOf K K',
        c ≠ .patch (p t ht) ∧ section34BoundedDim c = 2 ∧
          src (.faceArc a) ⊆ src c ∧ src c ⊆ srcBd (.vertexBall a.1.2) := by
      rcases hall (.patch (p t ht)) rfl (hAp t ht) (hpBd t ht) with hPf | hPg
      · exact ⟨g, fun hgP => hfg (hPf.symm.trans hgP.symm), hdg, hAg, hg⟩
      · exact ⟨f, fun hfP => hfg (hfP.trans hPg), hdf, hAf, hf⟩
    have hcV := hcBd.trans (hcut.srcBd_subset_src (.vertexBall a.1.2))
    cases c with
    | splitDisk e =>
      have h := (hcut.cutStep_iff_source_subset_splitDisk e rfl).2 hAc
      exact h.elim
    | faceDisk s => exact (hcut.not_faceDisk_subset_vertexBall s a.1.2 hcV).elim
    | patch x =>
      have hxw := hcut.patch_eq_of_subset_vertexBall x a.1.2 hcV
      have hAT : src (.faceArc a) ⊆ src (.tetraBall x.1.1) := by
        rw [hpatch x] at hAc
        exact hAc.trans inter_subset_left
      have hxs := (hcut.faceArc_subset_tetraBall_iff a x.1.1).1 hAT
      have hxt := hcut.tetra_eq_of_boundary_triangle a.1.1 hs hxs ht
      have hxp : x = p t ht := Subtype.ext (Prod.ext hxt hxw)
      exact (hcP (congrArg Section34BoundedLabel.patch hxp)).elim
    | outerFace o' =>
      have hoo : o' = o := Subtype.ext
        (((hcut.outerFace_subset_vertexBall_iff o' a.1.2).1 hcV).trans hwo)
      simpa only [hoo] using hAc
    | _ => simp [section34BoundedDim] at hdc

theorem Section34CompactCutFrame.markedPoint_subset_outerArc_iff
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (p : Section34CompactMarkIndex K K') (q : Section34CompactOuterEdgeIndex K K') :
    src (.markedPoint p) ⊆ src (.outerArc q) ↔ p.1.2 = q.1 ∧
      convexHull ℝ (p.1.1.1 : Set E3) ⊆ frontier K.space := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, hmark, -, hedge, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hex⟩ := id hcut
  have hPD : src (.markedPoint p) ⊆ src (.splitDisk p.1.2) := by
    rw [hmark p]
    exact inter_subset_left
  have hQD := hcut.outerArc_subset_splitDisk q
  let i (t : Section34CompactSimplexIndex K 4) (ht : Section34Incident p.1.1.1 t.1) :
      Section34CompactEdgeArcIndex K K' :=
    ⟨(t, p.1.2), p.2.trans (convexHull_min ht (convex_convexHull ℝ _))⟩
  have hPi (t : Section34CompactSimplexIndex K 4) (ht : Section34Incident p.1.1.1 t.1) :
      src (.markedPoint p) ⊆ src (.edgeArc (i t ht)) :=
    (hcut.markedPoint_subset_edgeArc_iff p (i t ht)).2 ⟨rfl, ht⟩
  have hiD (t : Section34CompactSimplexIndex K 4) (ht : Section34Incident p.1.1.1 t.1) :
      src (.edgeArc (i t ht)) ⊆ src (.splitDisk p.1.2) := by
    rw [hedge (i t ht)]
    exact inter_subset_right
  have hiBd (t : Section34CompactSimplexIndex K 4) (ht : Section34Incident p.1.1.1 t.1) :
      src (.edgeArc (i t ht)) ⊆ srcBd (.splitDisk p.1.2) :=
    source_subset_boundary_of_ne hcut (hiD t ht) (by simp)
  constructor
  · intro hPQ
    have he : p.1.2 = q.1 := by
      by_contra he
      obtain ⟨z, hz⟩ := (hcell (.markedPoint p)).nonempty
      exact Set.disjoint_left.mp (hcut.disjoint_splitDisk he) (hPD hz) (hQD (hPQ hz))
    refine ⟨he, ?_⟩
    have hQD' : src (.outerArc q) ⊆ src (.splitDisk p.1.2) := by
      rw [he]
      exact hQD
    have hQBd := source_subset_boundary_of_ne hcut hQD' (by simp)
    by_contra hs
    obtain ⟨t, u, htu, ht, hu⟩ := hcut.exists_tetra_pair_of_not_boundary_triangle p.1.1 hs
    obtain ⟨f, g, -, -, -, -, -, -, -, hall⟩ :=
      CompactSourceFaceProbe.split_disk_boundary_thin hcut p.1.2 p (hPQ.trans hQBd)
    have hA := hall (.edgeArc (i t ht)) rfl (hPi t ht) (hiBd t ht)
    have hB := hall (.edgeArc (i u hu)) rfl (hPi u hu) (hiBd u hu)
    have hO := hall (.outerArc q) rfl hPQ hQBd
    have hne : (.edgeArc (i t ht) : Section34CompactLabelOf K K') ≠ .edgeArc (i u hu) := by
      intro h
      exact htu (congrArg (fun x : Section34CompactEdgeArcIndex K K' => x.1.1)
        (Section34BoundedLabel.edgeArc.inj h))
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> rcases hO with hO | hO
    all_goals first
      | exact hne (hA.trans hB.symm)
      | cases hA.trans hO.symm
      | cases hB.trans hO.symm
  · rintro ⟨he, hs⟩
    obtain ⟨t, ht⟩ := hex p.1.1
    obtain ⟨f, g, hfg, hdf, hdg, hPf, hf, hPg, hg, hall⟩ :=
      CompactSourceFaceProbe.split_disk_boundary_thin hcut p.1.2 p ((hPi t ht).trans (hiBd t ht))
    obtain ⟨c, hci, hdc, hPc, hcBd⟩ : ∃ c : Section34CompactLabelOf K K',
        c ≠ .edgeArc (i t ht) ∧ section34BoundedDim c = 1 ∧
          src (.markedPoint p) ⊆ src c ∧ src c ⊆ srcBd (.splitDisk p.1.2) := by
      rcases hall (.edgeArc (i t ht)) rfl (hPi t ht) (hiBd t ht) with hif | hig
      · exact ⟨g, fun hgi => hfg (hif.symm.trans hgi.symm), hdg, hPg, hg⟩
      · exact ⟨f, fun hfi => hfg (hfi.trans hig), hdf, hPf, hf⟩
    have hcD := hcBd.trans (hcut.srcBd_subset_src (.splitDisk p.1.2))
    have hstep := (hcut.cutStep_iff_source_subset_splitDisk p.1.2 hdc).2 hcD
    cases c with
    | edgeArc j =>
      have hje : j.1.2 = p.1.2 := hstep
      have hsj := ((hcut.markedPoint_subset_edgeArc_iff p j).1 hPc).2
      have hjt := hcut.tetra_eq_of_boundary_triangle p.1.1 hs hsj ht
      have hji : j = i t ht := Subtype.ext (Prod.ext hjt hje)
      exact (hci (congrArg Section34BoundedLabel.edgeArc hji)).elim
    | outerArc q' =>
      have hqe : q'.1 = p.1.2 := hstep
      have hqq : q' = q := Subtype.ext (hqe.trans he)
      simpa only [hqq] using hPc
    | _ => simp [Section34CompactCutStep] at hstep

end DifferentialGeometry.Topology.PiecewiseLinear
