/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFacePoset

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

theorem Section34CompactCutFrame.splitDisk_subset_vertexBall_iff
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (e : Section34CompactEdgeIndex K K') (w : Section34CompactVertexIndex K K') :
    src (.splitDisk e) ⊆ src (.vertexBall w) ↔ w.1 ⊆ e.1 := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hmeet, hends, -⟩ := id hcut
  constructor
  · intro hsub
    obtain ⟨x, hx⟩ := (hcell (.splitDisk e)).nonempty
    exact hmeet w e ⟨x, hsub hx, hx⟩
  · intro hwe
    obtain ⟨a, b, -, hab, he⟩ := hends e
    rcases eq_or_eq_of_section34CompactVertexIndex_subset e hab hwe with rfl | rfl
    · rw [he]
      exact inter_subset_left
    · rw [he]
      exact inter_subset_right

theorem Section34CompactCutFrame.outerFace_subset_vertexBall_iff
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (o : Section34CompactOuterVertexIndex K K') (w : Section34CompactVertexIndex K K') :
    src (.outerFace o) ⊆ src (.vertexBall w) ↔ o.1 = w := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, -, -, -, hout, -⟩ := id hcut
  have hown : src (.outerFace o) ⊆ src (.vertexBall o.1) := by
    rw [hout o, ← (hcell (.vertexBall o.1)).isCompact.isClosed.closure_eq]
    exact closure_mono (sdiff_subset.trans (hcell (.vertexBall o.1)).boundary_subset)
  constructor
  · intro hsub
    by_contra hne
    exact hcut.not_outerFace_subset_inter_vertexBall o hne hown hsub
  · rintro rfl
    exact hown

theorem Section34CompactCutFrame.cutStep_iff_source_subset_vertexBall
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m : Section34CompactLabelOf K K'} (w : Section34CompactVertexIndex K K')
    (hd : section34BoundedDim m = 2) :
    Section34CompactCutStep m (.vertexBall w) ↔ src m ⊆ src (.vertexBall w) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hpatch, -⟩ := id hcut
  cases m with
  | splitDisk e => exact (hcut.splitDisk_subset_vertexBall_iff e w).symm
  | faceDisk s =>
    exact ⟨False.elim, fun hsub => hcut.not_faceDisk_subset_vertexBall s w hsub⟩
  | patch x =>
    constructor
    · intro hx
      change x.1.2 = w at hx
      rw [hpatch x, ← hx]
      exact inter_subset_right
    · exact hcut.patch_eq_of_subset_vertexBall x w
  | outerFace o => exact (hcut.outerFace_subset_vertexBall_iff o w).symm
  | _ => simp [section34BoundedDim] at hd

theorem Section34CompactCutFrame.disjoint_splitDisk
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {e e' : Section34CompactEdgeIndex K K'} (hee : e ≠ e') :
    Disjoint (src (.splitDisk e)) (src (.splitDisk e')) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hmeet, hends, -⟩ := id hcut
  refine Set.disjoint_left.mpr fun x hx hx' => hee ?_
  have hsub : ∀ a b : Section34CompactEdgeIndex K K',
      x ∈ src (.splitDisk a) → x ∈ src (.splitDisk b) → b.1 ⊆ a.1 := by
    intro a b ha hb
    obtain ⟨v, v', -, hbv, hb'⟩ := hends b
    rw [hb'] at hb
    rw [← Finset.coe_subset, hbv]
    exact union_subset (Finset.coe_subset.mpr (hmeet v a ⟨x, hb.1, ha⟩))
      (Finset.coe_subset.mpr (hmeet v' a ⟨x, hb.2, ha⟩))
  exact Subtype.ext (Finset.Subset.antisymm (hsub e' e hx' hx) (hsub e e' hx hx'))

theorem Section34CompactCutFrame.patch_subset_tetraBall_iff
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (x : Section34CompactPatchIndex K K') (t : Section34CompactSimplexIndex K 4) :
    src (.patch x) ⊆ src (.tetraBall t) ↔ x.1.1 = t := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, -, hpatch, -, -, -, -, -, -, -,
    havoid, -⟩ := id hcut
  have hV : src (.patch x) ⊆ src (.vertexBall x.1.2) := by
    rw [hpatch x]
    exact inter_subset_right
  constructor
  · intro hsub
    have hi : Section34Incident x.1.2.1 t.1 := by
      by_contra hi
      obtain ⟨z, hz⟩ := (hcell (.patch x)).nonempty
      have hmem : z ∈ src (.tetraBall t) ∩ src (.vertexBall x.1.2) := ⟨hsub hz, hV hz⟩
      rw [havoid t x.1.2 hi] at hmem
      exact hmem
    let y : Section34CompactPatchIndex K K' := ⟨(t, x.1.2), hi⟩
    have hxy : src (.patch x) ⊆ src (.patch y) := by
      rw [hpatch y]
      exact subset_inter hsub hV
    have heq := hcut.eq_of_subset_of_dim_le hxy le_rfl
    exact congrArg (fun z : Section34CompactPatchIndex K K' => z.1.1)
      (Section34BoundedLabel.patch.inj heq)
  · intro hxt
    rw [hpatch x, hxt]
    exact inter_subset_left

theorem Section34CompactCutFrame.not_splitDisk_subset_tetraBall
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (e : Section34CompactEdgeIndex K K') (t : Section34CompactSimplexIndex K 4) :
    ¬ src (.splitDisk e) ⊆ src (.tetraBall t) := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, -, -, hedge, -, -, -, -, -, -, -,
    havoid, -⟩ := id hcut
  intro hsub
  have hi : Section34Incident e.1 t.1 := by
    by_contra hi
    obtain ⟨z, hz⟩ := (hcell (.splitDisk e)).nonempty
    have hmem : z ∈ src (.tetraBall t) ∩ src (.splitDisk e) := ⟨hsub hz, hz⟩
    rw [havoid t e hi] at hmem
    exact hmem
  let i : Section34CompactEdgeArcIndex K K' := ⟨(t, e), hi⟩
  have hsi : src (.splitDisk e) ⊆ src (.edgeArc i) := by
    rw [hedge i]
    exact subset_inter hsub subset_rfl
  have heq := hcut.eq_of_subset_of_dim_le hsi (by simp [section34BoundedDim])
  simp at heq

private theorem not_one_cell_subset_splitDisk_inter_faceDisk
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m : Section34CompactLabelOf K K'} (hm : section34BoundedDim m = 1)
    (e : Section34CompactEdgeIndex K K') (s : Section34CompactSimplexIndex K 3)
    (he : src m ⊆ src (.splitDisk e)) (hs : src m ⊆ src (.faceDisk s)) : False := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, hmark, -, -, -, -, -, -, -,
    havoid, -⟩ := id hcut
  have hi : Section34Incident e.1 s.1 := by
    by_contra hi
    obtain ⟨z, hz⟩ := (hcell m).nonempty
    have hmem : z ∈ src (.faceDisk s) ∩ src (.splitDisk e) := ⟨hs hz, he hz⟩
    rw [havoid s e hi] at hmem
    exact hmem
  let p : Section34CompactMarkIndex K K' := ⟨(s, e), hi⟩
  have hmp : src m ⊆ src (.markedPoint p) := by
    rw [hmark p]
    exact subset_inter he hs
  have heq := hcut.eq_of_subset_of_dim_le hmp (Nat.zero_le _)
  have hd := congrArg section34BoundedDim heq
  change section34BoundedDim m = 0 at hd
  omega

theorem Section34CompactCutFrame.cutStep_iff_source_subset_splitDisk
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m : Section34CompactLabelOf K K'} (e : Section34CompactEdgeIndex K K')
    (hd : section34BoundedDim m = 1) :
    Section34CompactCutStep m (.splitDisk e) ↔ src m ⊆ src (.splitDisk e) := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, harc, -, -, hedge, -⟩ := id hcut
  have heq (e' : Section34CompactEdgeIndex K K') (l : Section34CompactLabelOf K K')
      (hl : src l ⊆ src (.splitDisk e')) (hl' : src l ⊆ src (.splitDisk e)) : e' = e := by
    by_contra hne
    obtain ⟨z, hz⟩ := (hcell l).nonempty
    exact Set.disjoint_left.mp (hcut.disjoint_splitDisk hne) (hl hz) (hl' hz)
  cases m with
  | faceArc a =>
    refine ⟨False.elim, fun hsub => ?_⟩
    have hs : src (.faceArc a) ⊆ src (.faceDisk a.1.1) := by
      rw [harc a]
      exact inter_subset_right
    exact not_one_cell_subset_splitDisk_inter_faceDisk hcut rfl e a.1.1 hsub hs
  | edgeArc i =>
    have hi : src (.edgeArc i) ⊆ src (.splitDisk i.1.2) := by
      rw [hedge i]
      exact inter_subset_right
    exact ⟨fun h => h ▸ hi, heq i.1.2 (.edgeArc i) hi⟩
  | outerArc q =>
    have hq := hcut.outerArc_subset_splitDisk q
    exact ⟨fun h => h ▸ hq, heq q.1 (.outerArc q) hq⟩
  | _ => simp [section34BoundedDim] at hd

theorem Section34CompactCutFrame.cutStep_iff_source_subset_faceDisk
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m : Section34CompactLabelOf K K'} (s : Section34CompactSimplexIndex K 3)
    (hd : section34BoundedDim m = 1) :
    Section34CompactCutStep m (.faceDisk s) ↔ src m ⊆ src (.faceDisk s) := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, harc, -, -, hedge, -, -, -, -,
    havoid, -⟩ := id hcut
  cases m with
  | faceArc a =>
    constructor
    · intro h
      change a.1.1 = s at h
      rw [harc a, h]
      exact inter_subset_right
    · intro hsub
      have hv : src (.faceArc a) ⊆ src (.vertexBall a.1.2) := by
        rw [harc a]
        exact inter_subset_left
      have hi : Section34Incident a.1.2.1 s.1 := by
        by_contra hi
        obtain ⟨z, hz⟩ := (hcell (.faceArc a)).nonempty
        have hmem : z ∈ src (.faceDisk s) ∩ src (.vertexBall a.1.2) := ⟨hsub hz, hv hz⟩
        rw [havoid s a.1.2 hi] at hmem
        exact hmem
      let b : Section34CompactArcIndex K K' := ⟨(s, a.1.2), hi⟩
      have hab : src (.faceArc a) ⊆ src (.faceArc b) := by
        rw [harc b]
        exact subset_inter hv hsub
      have heq := hcut.eq_of_subset_of_dim_le hab le_rfl
      exact congrArg (fun z : Section34CompactArcIndex K K' => z.1.1)
        (Section34BoundedLabel.faceArc.inj heq)
  | edgeArc i =>
    refine ⟨False.elim, fun hsub => ?_⟩
    have he : src (.edgeArc i) ⊆ src (.splitDisk i.1.2) := by
      rw [hedge i]
      exact inter_subset_right
    exact not_one_cell_subset_splitDisk_inter_faceDisk hcut rfl i.1.2 s he hsub
  | outerArc q =>
    exact ⟨False.elim, fun hsub => not_one_cell_subset_splitDisk_inter_faceDisk hcut rfl
      q.1 s (hcut.outerArc_subset_splitDisk q) hsub⟩
  | _ => simp [section34BoundedDim] at hd

theorem Section34CompactCutFrame.cutStep_iff_source_subset_faceArc
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m : Section34CompactLabelOf K K'} (a : Section34CompactArcIndex K K')
    (hd : section34BoundedDim m = 0) :
    Section34CompactCutStep m (.faceArc a) ↔ src m ⊆ src (.faceArc a) := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, harc, hmark, -, -, -, -, -, -, -,
    havoid, -, -, -, -, hmeet, -⟩ := id hcut
  cases m <;> simp only [section34BoundedDim, Nat.reduceEqDiff] at hd
  rename_i p
  constructor
  · rintro ⟨hs, hw⟩
    rw [hmark p, harc a]
    exact fun z hz => ⟨(hcut.splitDisk_subset_vertexBall_iff p.1.2 a.1.2).2 hw hz.1,
      hs ▸ hz.2⟩
  · intro hsub
    have he : src (.markedPoint p) ⊆ src (.splitDisk p.1.2) := by
      rw [hmark p]
      exact inter_subset_left
    have hs : src (.markedPoint p) ⊆ src (.faceDisk a.1.1) := by
      rw [harc a] at hsub
      exact hsub.trans inter_subset_right
    obtain ⟨z, hz⟩ := (hcell (.markedPoint p)).nonempty
    have hw : a.1.2.1 ⊆ p.1.2.1 := hmeet a.1.2 p.1.2
      ⟨z, (harc a ▸ hsub hz).1, he hz⟩
    have hi : Section34Incident p.1.2.1 a.1.1.1 := by
      by_contra hi
      have hmem : z ∈ src (.faceDisk a.1.1) ∩ src (.splitDisk p.1.2) := ⟨hs hz, he hz⟩
      rw [havoid a.1.1 p.1.2 hi] at hmem
      exact hmem
    let q : Section34CompactMarkIndex K K' := ⟨(a.1.1, p.1.2), hi⟩
    have hpq : src (.markedPoint p) ⊆ src (.markedPoint q) := by
      rw [hmark q]
      exact subset_inter he hs
    have heq := hcut.eq_of_subset_of_dim_le hpq le_rfl
    exact ⟨congrArg (fun r : Section34CompactMarkIndex K K' => r.1.1)
      (Section34BoundedLabel.markedPoint.inj heq), hw⟩

end DifferentialGeometry.Topology.PiecewiseLinear
