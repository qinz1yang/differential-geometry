/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLCellOn.boundary_nonempty_two {S B : Set E3} (hS : IsPLCellOn 2 S B) :
    B.Nonempty := by
  obtain ⟨P, r, u, -, -, -, rfl⟩ := hS
  exact ⟨u (r (Pi.single 0 1)), r (Pi.single 0 1),
    ⟨Pi.single 0 1, ⟨Convexity.StdSimplex.single_mem_coordinateSet ℝ 0, 1,
      Pi.single_eq_of_ne (show (1 : Fin 3) ≠ 0 by decide) (1 : ℝ)⟩, rfl⟩, rfl⟩

section Cut

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

theorem Section34CompactCutFrame.eq_of_subset_of_dim_le
    (hcut : Section34CompactCutFrame C K K' src srcBd) {l m : Section34CompactLabelOf K K'}
    (hsub : src l ⊆ src m) (hd : section34BoundedDim m ≤ section34BoundedDim l) : l = m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hdim, -⟩ := hcut
  rcases hdim m l hsub with heq | hlt
  · exact heq
  · omega

theorem eq_or_eq_of_section34CompactVertexIndex_subset (e : Section34CompactEdgeIndex K K')
    {a b v : Section34CompactVertexIndex K K'}
    (hab : (e.1 : Set E3) = (a.1 : Set E3) ∪ (b.1 : Set E3)) (hve : v.1 ⊆ e.1) :
    v = a ∨ v = b := by
  have hvertexEq {u u' : Section34CompactVertexIndex K K'} {z : E3}
      (hz : z ∈ u.1) (hz' : z ∈ u'.1) : u = u' := by
    apply Subtype.ext
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp u.2.2.1
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp u'.2.2.1
    have hpq : p = q := (Finset.mem_singleton.mp (hp ▸ hz)).symm.trans
      (Finset.mem_singleton.mp (hq ▸ hz'))
    exact hp.trans ((congrArg (fun z : E3 => ({z} : Finset E3)) hpq).trans hq.symm)
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp v.2.2.1
  have hzv : z ∈ v.1 := hz.symm ▸ Finset.mem_singleton_self z
  have hze : z ∈ (e.1 : Set E3) := hve hzv
  rw [hab] at hze
  exact hze.elim (fun hza => Or.inl (hvertexEq hzv hza)) (fun hzb => Or.inr (hvertexEq hzv hzb))

theorem Section34CompactCutFrame.splitDisk_eq_inter_vertexBall
    (hcut : Section34CompactCutFrame C K K' src srcBd) (e : Section34CompactEdgeIndex K K')
    {v v' : Section34CompactVertexIndex K K'} (hvv : v ≠ v')
    (hv : (src (.vertexBall v) ∩ src (.splitDisk e)).Nonempty)
    (hv' : (src (.vertexBall v') ∩ src (.splitDisk e)).Nonempty) :
    src (.splitDisk e) = src (.vertexBall v) ∩ src (.vertexBall v') := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hvertexEdge, hends, -, -⟩ := id hcut
  obtain ⟨a, b, -, hab, he⟩ := hends e
  rcases eq_or_eq_of_section34CompactVertexIndex_subset e hab (hvertexEdge v e hv) with h1 | h1 <;>
    rcases eq_or_eq_of_section34CompactVertexIndex_subset e hab (hvertexEdge v' e hv') with h2 | h2
  · exact (hvv (h1.trans h2.symm)).elim
  · rw [h1, h2]
    exact he
  · rw [h1, h2]
    exact he.trans (inter_comm _ _)
  · exact (hvv (h1.trans h2.symm)).elim

theorem Section34CompactCutFrame.faceArc_eq_of_subset_vertexBall
    (hcut : Section34CompactCutFrame C K K' src srcBd) (a : Section34CompactArcIndex K K')
    (v : Section34CompactVertexIndex K K')
    (hsub : src (.faceArc a) ⊆ src (.vertexBall v)) : a.1.2 = v := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, harc, -, -, -, -, -, -, -, hfaceVertex, -⟩ :=
    id hcut
  have hsubF : src (.faceArc a) ⊆ src (.faceDisk a.1.1) := by
    rw [harc a]
    exact inter_subset_right
  obtain ⟨x, hx⟩ := (hcell (.faceArc a)).nonempty
  have hi : Section34Incident v.1 a.1.1.1 := by
    by_contra hi
    have hx' : x ∈ src (.faceDisk a.1.1) ∩ src (.vertexBall v) := ⟨hsubF hx, hsub hx⟩
    rw [hfaceVertex a.1.1 v hi] at hx'
    exact hx'
  let b : Section34CompactArcIndex K K' := ⟨(a.1.1, v), hi⟩
  have hab : src (.faceArc a) ⊆ src (.faceArc b) := by
    rw [harc b]
    exact fun y hy => ⟨hsub hy, hsubF hy⟩
  have hab' := hcut.eq_of_subset_of_dim_le hab le_rfl
  exact congrArg (fun r : Section34CompactArcIndex K K' => r.1.2)
    (Section34BoundedLabel.faceArc.inj hab')

theorem Section34CompactCutFrame.patch_eq_of_subset_vertexBall
    (hcut : Section34CompactCutFrame C K K' src srcBd) (p : Section34CompactPatchIndex K K')
    (v : Section34CompactVertexIndex K K')
    (hsub : src (.patch p) ⊆ src (.vertexBall v)) : p.1.2 = v := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, -, hpatch, -, -, -, -, -, -, -,
    htetraVertex, -⟩ := id hcut
  have hsubT : src (.patch p) ⊆ src (.tetraBall p.1.1) := by
    rw [hpatch p]
    exact inter_subset_left
  obtain ⟨x, hx⟩ := (hcell (.patch p)).nonempty
  have hi : Section34Incident v.1 p.1.1.1 := by
    by_contra hi
    have hx' : x ∈ src (.tetraBall p.1.1) ∩ src (.vertexBall v) := ⟨hsubT hx, hsub hx⟩
    rw [htetraVertex p.1.1 v hi] at hx'
    exact hx'
  let q : Section34CompactPatchIndex K K' := ⟨(p.1.1, v), hi⟩
  have hpq : src (.patch p) ⊆ src (.patch q) := by
    rw [hpatch q]
    exact fun y hy => ⟨hsubT hy, hsub hy⟩
  have hpq' := hcut.eq_of_subset_of_dim_le hpq le_rfl
  exact congrArg (fun r : Section34CompactPatchIndex K K' => r.1.2)
    (Section34BoundedLabel.patch.inj hpq')

theorem Section34CompactCutFrame.not_faceDisk_subset_vertexBall
    (hcut : Section34CompactCutFrame C K K' src srcBd) (s : Section34CompactSimplexIndex K 3)
    (v : Section34CompactVertexIndex K K') : ¬ src (.faceDisk s) ⊆ src (.vertexBall v) := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, harc, -, -, -, -, -, -, -, hfaceVertex, -⟩ :=
    id hcut
  intro hsub
  obtain ⟨x, hx⟩ := (hcell (.faceDisk s)).nonempty
  have hi : Section34Incident v.1 s.1 := by
    by_contra hi
    have hx' : x ∈ src (.faceDisk s) ∩ src (.vertexBall v) := ⟨hx, hsub hx⟩
    rw [hfaceVertex s v hi] at hx'
    exact hx'
  let a : Section34CompactArcIndex K K' := ⟨(s, v), hi⟩
  have hsubArc : src (.faceDisk s) ⊆ src (.faceArc a) := by
    rw [harc a]
    exact fun y hy => ⟨hsub hy, hy⟩
  have := hcut.eq_of_subset_of_dim_le hsubArc (by simp [section34BoundedDim])
  simp at this

theorem Section34CompactCutFrame.outerArc_subset_splitDisk
    (hcut : Section34CompactCutFrame C K K' src srcBd) (q : Section34CompactOuterEdgeIndex K K') :
    src (.outerArc q) ⊆ src (.splitDisk q.1) := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, -, -, -, -, houtA, -⟩ := id hcut
  rw [houtA q, ← (hcell (.splitDisk q.1)).isCompact.isClosed.closure_eq]
  exact closure_mono (sdiff_subset.trans (hcell (.splitDisk q.1)).boundary_subset)

theorem Section34CompactCutFrame.not_outerFace_subset_inter_vertexBall
    (hcut : Section34CompactCutFrame C K K' src srcBd) (o : Section34CompactOuterVertexIndex K K')
    {v v' : Section34CompactVertexIndex K K'} (hvv : v ≠ v')
    (hv : src (.outerFace o) ⊆ src (.vertexBall v))
    (hv' : src (.outerFace o) ⊆ src (.vertexBall v')) : False := by
  obtain ⟨-, -, -, -, -, -, hcell, hbd, -, -, -, -, hmark, -, hedge, -⟩ := id hcut
  have hSD : ∀ (e : Section34CompactEdgeIndex K K') (X : Set E3), X.Nonempty →
      X ⊆ src (.splitDisk e) → X ⊆ src (.outerFace o) → False := by
    intro e X hX hXe hXo
    obtain ⟨x, hx⟩ := hX
    have heq := hcut.splitDisk_eq_inter_vertexBall e hvv ⟨x, hv (hXo hx), hXe hx⟩
      ⟨x, hv' (hXo hx), hXe hx⟩
    have hsub : src (.outerFace o) ⊆ src (.splitDisk e) := by
      rw [heq]
      exact subset_inter hv hv'
    have := hcut.eq_of_subset_of_dim_le hsub le_rfl
    simp at this
  obtain ⟨z, hz⟩ := (hcell (.outerFace o)).boundary_nonempty_two
  rw [hbd (.outerFace o)] at hz
  obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp hz
  have hmsub : src m ⊆ src (.outerFace o) := hm.1
  have hmne : m ≠ .outerFace o := hm.2
  cases m with
  | vertexBall u =>
    exact hmne (hcut.eq_of_subset_of_dim_le hmsub (by simp [section34BoundedDim]))
  | tetraBall t =>
    exact hmne (hcut.eq_of_subset_of_dim_le hmsub (by simp [section34BoundedDim]))
  | splitDisk e =>
    exact hmne (hcut.eq_of_subset_of_dim_le hmsub (by simp [section34BoundedDim]))
  | faceDisk s =>
    exact hmne (hcut.eq_of_subset_of_dim_le hmsub (by simp [section34BoundedDim]))
  | patch x =>
    exact hmne (hcut.eq_of_subset_of_dim_le hmsub (by simp [section34BoundedDim]))
  | outerFace o' =>
    exact hmne (hcut.eq_of_subset_of_dim_le hmsub (by simp [section34BoundedDim]))
  | faceArc a =>
    exact hvv ((hcut.faceArc_eq_of_subset_vertexBall a v (hmsub.trans hv)).symm.trans
      (hcut.faceArc_eq_of_subset_vertexBall a v' (hmsub.trans hv')))
  | edgeArc i =>
    refine hSD i.1.2 _ (hcell (.edgeArc i)).nonempty ?_ hmsub
    rw [hedge i]
    exact inter_subset_right
  | markedPoint p =>
    refine hSD p.1.2 _ (hcell (.markedPoint p)).nonempty ?_ hmsub
    rw [hmark p]
    exact inter_subset_left
  | outerArc q =>
    exact hSD q.1 _ (hcell (.outerArc q)).nonempty (hcut.outerArc_subset_splitDisk q) hmsub

theorem Section34CompactCutFrame.exists_splitDisk_eq_inter_vertexBall
    (hcut : Section34CompactCutFrame C K K' src srcBd) {w w' : Section34CompactVertexIndex K K'}
    (hww : w ≠ w') (hmeet : (src (.vertexBall w) ∩ src (.vertexBall w')).Nonempty) :
    ∃ e : Section34CompactEdgeIndex K K',
      src (.splitDisk e) = src (.vertexBall w) ∩ src (.vertexBall w') := by
  obtain ⟨-, -, -, -, -, -, -, -, hinter, -, -, -, hmark, -, hedge, -⟩ := id hcut
  obtain ⟨x, hxw, hxw'⟩ := hmeet
  have hx : x ∈ src (.vertexBall w) ∩ src (.vertexBall w') := ⟨hxw, hxw'⟩
  rw [hinter] at hx
  obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.mp hx
  have hlw : src l ⊆ src (.vertexBall w) := hl.1
  have hlw' : src l ⊆ src (.vertexBall w') := hl.2
  have hSD : ∀ e : Section34CompactEdgeIndex K K', x ∈ src (.splitDisk e) →
      ∃ e' : Section34CompactEdgeIndex K K',
        src (.splitDisk e') = src (.vertexBall w) ∩ src (.vertexBall w') := fun e hxe =>
    ⟨e, hcut.splitDisk_eq_inter_vertexBall e hww ⟨x, hxw, hxe⟩ ⟨x, hxw', hxe⟩⟩
  cases l with
  | vertexBall v =>
    have h1 := hcut.eq_of_subset_of_dim_le hlw le_rfl
    have h2 := hcut.eq_of_subset_of_dim_le hlw' le_rfl
    exact (hww (Section34BoundedLabel.vertexBall.inj (h1.symm.trans h2))).elim
  | tetraBall t =>
    have := hcut.eq_of_subset_of_dim_le hlw le_rfl
    simp at this
  | splitDisk e => exact hSD e hxl
  | faceDisk s => exact (hcut.not_faceDisk_subset_vertexBall s w hlw).elim
  | patch p =>
    exact (hww ((hcut.patch_eq_of_subset_vertexBall p w hlw).symm.trans
      (hcut.patch_eq_of_subset_vertexBall p w' hlw'))).elim
  | faceArc a =>
    exact (hww ((hcut.faceArc_eq_of_subset_vertexBall a w hlw).symm.trans
      (hcut.faceArc_eq_of_subset_vertexBall a w' hlw'))).elim
  | edgeArc i =>
    rw [hedge i] at hxl
    exact hSD i.1.2 hxl.2
  | markedPoint p =>
    rw [hmark p] at hxl
    exact hSD p.1.2 hxl.1
  | outerFace o => exact (hcut.not_outerFace_subset_inter_vertexBall o hww hlw hlw').elim
  | outerArc q => exact hSD q.1 (hcut.outerArc_subset_splitDisk q hxl)

end Cut

end DifferentialGeometry.Topology.PiecewiseLinear
