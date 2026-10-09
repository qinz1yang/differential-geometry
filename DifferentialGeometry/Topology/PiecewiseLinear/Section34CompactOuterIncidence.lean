/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBoundaryThinness
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSourceIncidence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

theorem Section34CompactCutFrame.faceDisk_subset_base
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (s : Section34CompactSimplexIndex K 3) : src (.faceDisk s) ⊆ C := by
  obtain ⟨hC, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hface, -⟩ := hcut
  rw [hface s, ← hC]
  exact (closure_minimal sdiff_subset
    (s.1.finite_toSet.isCompact_convexHull ℝ).isClosed).trans (K.convexHull_subset_space s.2.1)

theorem Section34CompactCutFrame.tetraBall_subset_base
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (t : Section34CompactSimplexIndex K 4) : src (.tetraBall t) ⊆ C := by
  obtain ⟨hC, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htetra, -⟩ := hcut
  rw [htetra t, ← hC]
  exact (closure_minimal sdiff_subset
    (t.1.finite_toSet.isCompact_convexHull ℝ).isClosed).trans (K.convexHull_subset_space t.2.1)

theorem Section34CompactCutFrame.outerArc_sdiff_base_nonempty
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (q : Section34CompactOuterEdgeIndex K K') : (src (.outerArc q) \ C).Nonempty := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, -, -, -, -, hout, -⟩ := hcut
  have hnon := (hcell (.outerArc q)).nonempty
  rw [hout q] at hnon ⊢
  obtain ⟨x, hx⟩ := hnon.of_closure
  exact ⟨x, subset_closure hx, hx.2⟩

theorem Section34CompactCutFrame.outerFace_sdiff_base_nonempty
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (o : Section34CompactOuterVertexIndex K K') : (src (.outerFace o) \ C).Nonempty := by
  obtain ⟨-, -, -, -, -, -, hcell, -, -, -, -, -, -, -, -, hout, -⟩ := hcut
  have hnon := (hcell (.outerFace o)).nonempty
  rw [hout o] at hnon ⊢
  obtain ⟨x, hx⟩ := hnon.of_closure
  exact ⟨x, subset_closure hx, fun h => hx.2 (Or.inl h)⟩

theorem Section34CompactCutFrame.outerArc_subset_outerFace_iff
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (q : Section34CompactOuterEdgeIndex K K') (o : Section34CompactOuterVertexIndex K K') :
    src (.outerArc q) ⊆ src (.outerFace o) ↔ o.1.1 ⊆ q.1.1 := by
  obtain ⟨-, -, -, -, -, -, -, hbd, -, -, -, -, -, hpatch, -, -, -, -, -, -, -, -, -, -, -,
    hmeet, -⟩ := id hcut
  have hqD := hcut.outerArc_subset_splitDisk q
  have hoV := (hcut.outerFace_subset_vertexBall_iff o o.1).2 rfl
  obtain ⟨z, hzq, hzC⟩ := hcut.outerArc_sdiff_base_nonempty q
  constructor
  · intro hsub
    exact hmeet o.1 q.1 ⟨z, hoV (hsub hzq), hqD hzq⟩
  · intro how
    have hDV := (hcut.splitDisk_subset_vertexBall_iff q.1 o.1).2 how
    have hDBd : src (.splitDisk q.1) ⊆ srcBd (.vertexBall o.1) := by
      rw [hbd (.vertexBall o.1)]
      exact subset_iUnion₂_of_subset (.splitDisk q.1) ⟨hDV, by simp⟩ subset_rfl
    obtain ⟨a, b, hab, hda, hdb, hqa, ha, hqb, hb, hall⟩ :=
      CompactSourceFaceProbe.vertex_ball_boundary_thin hcut o.1 (.outerArc q) rfl
        (hqD.trans hDBd)
    obtain ⟨c, hcD, hdc, hqc, hcBd⟩ : ∃ c : Section34CompactLabelOf K K',
        c ≠ .splitDisk q.1 ∧ section34BoundedDim c = 2 ∧
          src (.outerArc q) ⊆ src c ∧ src c ⊆ srcBd (.vertexBall o.1) := by
      rcases hall (.splitDisk q.1) rfl hqD hDBd with hDa | hDb
      · exact ⟨b, fun hbD => hab (hDa.symm.trans hbD.symm), hdb, hqb, hb⟩
      · exact ⟨a, fun haD => hab (haD.trans hDb), hda, hqa, ha⟩
    have hcV := hcBd.trans (hcut.srcBd_subset_src (.vertexBall o.1))
    cases c with
    | splitDisk e =>
      have heq : e = q.1 := by
        by_contra heq
        exact Set.disjoint_left.mp (hcut.disjoint_splitDisk heq) (hqc hzq) (hqD hzq)
      exact (hcD (congrArg Section34BoundedLabel.splitDisk heq)).elim
    | faceDisk s => exact (hzC (hcut.faceDisk_subset_base s (hqc hzq))).elim
    | patch x =>
      have hqT : z ∈ src (.tetraBall x.1.1) := by
        have hzx := hqc hzq
        rw [hpatch x] at hzx
        exact hzx.1
      exact (hzC (hcut.tetraBall_subset_base x.1.1 hqT)).elim
    | outerFace o' =>
      have hoo : o' = o :=
        Subtype.ext ((hcut.outerFace_subset_vertexBall_iff o' o.1).mp hcV)
      simpa only [hoo] using hqc
    | _ => simp [section34BoundedDim] at hdc

theorem Section34CompactCutFrame.not_edgeArc_subset_outerFace
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (i : Section34CompactEdgeArcIndex K K') (o : Section34CompactOuterVertexIndex K K') :
    ¬ src (.edgeArc i) ⊆ src (.outerFace o) := by
  obtain ⟨-, -, -, -, -, -, hcell, hbd, -, -, -, -, -, hpatch, hedge, -, -, -, -, -, -, -, -, -, -,
    hmeet, -⟩ := id hcut
  intro hsub
  have hiD : src (.edgeArc i) ⊆ src (.splitDisk i.1.2) := by
    rw [hedge i]
    exact inter_subset_right
  have hiT : src (.edgeArc i) ⊆ src (.tetraBall i.1.1) := by
    rw [hedge i]
    exact inter_subset_left
  have hoV := (hcut.outerFace_subset_vertexBall_iff o o.1).2 rfl
  obtain ⟨z, hz⟩ := (hcell (.edgeArc i)).nonempty
  have hwe := hmeet o.1 i.1.2 ⟨z, hoV (hsub hz), hiD hz⟩
  have hwt : Section34Incident o.1.1 i.1.1.1 := fun x hx => i.2 (hwe hx)
  let p : Section34CompactPatchIndex K K' := ⟨(i.1.1, o.1), hwt⟩
  have hpV : src (.patch p) ⊆ src (.vertexBall o.1) := by
    rw [hpatch p]
    exact inter_subset_right
  have hip : src (.edgeArc i) ⊆ src (.patch p) := by
    rw [hpatch p]
    exact subset_inter hiT (hsub.trans hoV)
  have hproper {m : Section34CompactLabelOf K K'}
      (hm : src m ⊆ src (.vertexBall o.1)) (hne : m ≠ .vertexBall o.1) :
      src m ⊆ srcBd (.vertexBall o.1) := by
    rw [hbd (.vertexBall o.1)]
    exact subset_iUnion₂_of_subset m ⟨hm, hne⟩ subset_rfl
  have hDBd := hproper ((hcut.splitDisk_subset_vertexBall_iff i.1.2 o.1).2 hwe) (by simp)
  have hpBd := hproper hpV (by simp)
  have hoBd := hproper hoV (by simp)
  obtain ⟨a, b, -, -, -, -, -, -, -, hall⟩ :=
    CompactSourceFaceProbe.vertex_ball_boundary_thin hcut o.1 (.edgeArc i) rfl
      (hiD.trans hDBd)
  have hD := hall (.splitDisk i.1.2) rfl hiD hDBd
  have hP := hall (.patch p) rfl hip hpBd
  have hO := hall (.outerFace o) rfl hsub hoBd
  rcases hD with hD | hD
  · rcases hP with hP | hP
    · cases hD.trans hP.symm
    · rcases hO with hO | hO
      · cases hD.trans hO.symm
      · cases hP.trans hO.symm
  · rcases hP with hP | hP
    · rcases hO with hO | hO
      · cases hP.trans hO.symm
      · cases hD.trans hO.symm
    · cases hD.trans hP.symm

end DifferentialGeometry.Topology.PiecewiseLinear
