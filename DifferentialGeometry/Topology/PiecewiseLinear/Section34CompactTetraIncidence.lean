/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactArcEndpoints
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactIncidentEdges
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterIncidence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

theorem Section34CompactCutFrame.faceArc_subset_tetraBall_iff
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (a : Section34CompactArcIndex K K') (t : Section34CompactSimplexIndex K 4) :
    src (.faceArc a) ⊆ src (.tetraBall t) ↔ Section34Incident a.1.1.1 t.1 := by
  obtain ⟨-, -, hfin, -, hsub, -, hcell, -, -, -, -, harc, hmark, -, hedge, -, -, -, -, -, -, -,
    havoid, -, -, -, -, hface, -⟩ := id hcut
  constructor
  · intro hAT
    obtain ⟨e, -, -, hes, -, hwe, -, -⟩ :=
      exists_section34CompactEdgeIndex_pair_of_incident hsub hfin a.1.1 a.1.2 a.2
    let p : Section34CompactMarkIndex K K' := ⟨(a.1.1, e), hes⟩
    have hpA : src (.markedPoint p) ⊆ src (.faceArc a) :=
      (hcut.cutStep_iff_source_subset_faceArc a rfl).1 ⟨rfl, hwe⟩
    have hpE : src (.markedPoint p) ⊆ src (.splitDisk e) := by
      rw [hmark p]
      exact inter_subset_left
    have het : Section34Incident e.1 t.1 := by
      by_contra het
      obtain ⟨z, hz⟩ := (hcell (.markedPoint p)).nonempty
      have hmem : z ∈ src (.tetraBall t) ∩ src (.splitDisk e) :=
        ⟨hAT (hpA hz), hpE hz⟩
      rw [havoid t e het] at hmem
      exact hmem
    let i : Section34CompactEdgeArcIndex K K' := ⟨(t, e), het⟩
    have hpI : src (.markedPoint p) ⊆ src (.edgeArc i) := by
      rw [hedge i]
      exact subset_inter (hpA.trans hAT) hpE
    exact ((hcut.markedPoint_subset_edgeArc_iff p i).1 hpI).2
  · intro hat
    rw [harc a]
    exact inter_subset_right.trans (hface t a.1.1 hat)

theorem Section34CompactCutFrame.faceDisk_subset_tetraBall_iff
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (s : Section34CompactSimplexIndex K 3) (t : Section34CompactSimplexIndex K 4) :
    src (.faceDisk s) ⊆ src (.tetraBall t) ↔ Section34Incident s.1 t.1 := by
  classical
  obtain ⟨-, -, -, -, hsub, -, -, -, -, -, -, harc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hface, -⟩ := id hcut
  constructor
  · intro hST
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces s.2.1
    have hvK : {v} ∈ K.faces :=
      K.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    let w : Section34CompactVertexIndex K K' := ⟨{v}, hsub.singleton_mem hvK, by simp,
      by
        rw [Finset.coe_singleton, convexHull_singleton]
        exact fun x hx => mem_iUnion₂.mpr
          ⟨{v}, ⟨hvK, by simp⟩, by simpa only [Finset.coe_singleton, convexHull_singleton]
            using hx⟩⟩
    have hws : Section34Incident w.1 s.1 :=
      (Finset.coe_subset.mpr (Finset.singleton_subset_iff.mpr hv)).trans (subset_convexHull ℝ _)
    let a : Section34CompactArcIndex K K' := ⟨(s, w), hws⟩
    apply (hcut.faceArc_subset_tetraBall_iff a t).1
    rw [harc a]
    exact inter_subset_right.trans hST
  · exact hface t s

private theorem edgeArc_subset_tetraBall_iff
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (i : Section34CompactEdgeArcIndex K K') (t : Section34CompactSimplexIndex K 4) :
    src (.edgeArc i) ⊆ src (.tetraBall t) ↔ i.1.1 = t := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, -, -, hedge, -, -, -, -, -, -, -, havoid, -⟩ :=
    id hcut
  have hiE : src (.edgeArc i) ⊆ src (.splitDisk i.1.2) := by
    rw [hedge i]
    exact inter_subset_right
  constructor
  · intro hiT
    have het : Section34Incident i.1.2.1 t.1 := by
      by_contra het
      obtain ⟨z, hz⟩ := (hcell (.edgeArc i)).nonempty
      have hmem : z ∈ src (.tetraBall t) ∩ src (.splitDisk i.1.2) := ⟨hiT hz, hiE hz⟩
      rw [havoid t i.1.2 het] at hmem
      exact hmem
    let j : Section34CompactEdgeArcIndex K K' := ⟨(t, i.1.2), het⟩
    have hij : src (.edgeArc i) ⊆ src (.edgeArc j) := by
      rw [hedge j]
      exact subset_inter hiT hiE
    have heq := hcut.eq_of_subset_of_dim_le hij le_rfl
    exact congrArg (fun k : Section34CompactEdgeArcIndex K K' => k.1.1)
      (Section34BoundedLabel.edgeArc.inj heq)
  · intro hit
    rw [hedge i, hit]
    exact inter_subset_left

theorem Section34CompactCutFrame.cutStep_iff_source_subset_tetraBall
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m : Section34CompactLabelOf K K'} (t : Section34CompactSimplexIndex K 4)
    (hd : section34BoundedDim m = 2) :
    Section34CompactCutStep m (.tetraBall t) ↔ src m ⊆ src (.tetraBall t) := by
  cases m with
  | splitDisk e => exact ⟨False.elim, hcut.not_splitDisk_subset_tetraBall e t⟩
  | faceDisk s => exact (hcut.faceDisk_subset_tetraBall_iff s t).symm
  | patch x => exact (hcut.patch_subset_tetraBall_iff x t).symm
  | outerFace o =>
    refine ⟨False.elim, fun hsub => ?_⟩
    obtain ⟨z, hz, hzC⟩ := hcut.outerFace_sdiff_base_nonempty o
    exact hzC (hcut.tetraBall_subset_base t (hsub hz))
  | _ => simp [section34BoundedDim] at hd

theorem Section34CompactCutFrame.cutStep_iff_source_subset_patch
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m : Section34CompactLabelOf K K'} (x : Section34CompactPatchIndex K K')
    (hd : section34BoundedDim m = 1) :
    Section34CompactCutStep m (.patch x) ↔ src m ⊆ src (.patch x) := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, harc, -, hpatch, hedge, -, -, -, -, -, -, -, -, -, -,
    hmeet, -⟩ := id hcut
  rw [hpatch x]
  cases m with
  | faceArc a =>
    constructor
    · rintro ⟨hw, ht⟩
      refine subset_inter ((hcut.faceArc_subset_tetraBall_iff a x.1.1).2 ht) ?_
      rw [harc a, hw]
      exact inter_subset_left
    · intro hsub
      exact ⟨hcut.faceArc_eq_of_subset_vertexBall a x.1.2 (hsub.trans inter_subset_right),
        (hcut.faceArc_subset_tetraBall_iff a x.1.1).1 (hsub.trans inter_subset_left)⟩
  | edgeArc i =>
    have hiE : src (.edgeArc i) ⊆ src (.splitDisk i.1.2) := by
      rw [hedge i]
      exact inter_subset_right
    constructor
    · rintro ⟨ht, hw⟩
      exact subset_inter ((edgeArc_subset_tetraBall_iff hcut i x.1.1).2 ht)
        (hiE.trans ((hcut.splitDisk_subset_vertexBall_iff i.1.2 x.1.2).2 hw))
    · intro hsub
      obtain ⟨z, hz⟩ := (hcell (.edgeArc i)).nonempty
      exact ⟨(edgeArc_subset_tetraBall_iff hcut i x.1.1).1 (hsub.trans inter_subset_left),
        hmeet x.1.2 i.1.2 ⟨z, (hsub hz).2, hiE hz⟩⟩
  | outerArc q =>
    refine ⟨False.elim, fun hsub => ?_⟩
    obtain ⟨z, hz, hzC⟩ := hcut.outerArc_sdiff_base_nonempty q
    exact hzC (hcut.tetraBall_subset_base x.1.1 (hsub hz).1)
  | _ => simp [section34BoundedDim] at hd

theorem Section34CompactCutFrame.cutStep_iff_source_subset_edgeArc
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m : Section34CompactLabelOf K K'} (i : Section34CompactEdgeArcIndex K K')
    (hd : section34BoundedDim m = 0) :
    Section34CompactCutStep m (.edgeArc i) ↔ src m ⊆ src (.edgeArc i) := by
  cases m with
  | markedPoint p => exact (hcut.markedPoint_subset_edgeArc_iff p i).symm
  | _ => simp [section34BoundedDim] at hd

end DifferentialGeometry.Topology.PiecewiseLinear
