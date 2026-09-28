/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingBallSeam
import DifferentialGeometry.Topology.PiecewiseLinear.OutermostCircleCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

theorem Section34CompactCutFrame.not_arc_interior_on_split_disk_boundary
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (w : Section34CompactVertexIndex K K') (e : Section34CompactEdgeIndex K K')
    {J A : Set E3} {α : ℝ → E3} (hα : IsPLHomeomorphOn α (Icc 0 1) A)
    (hAJ : A ⊆ J) (hAV : A ⊆ section34CompactVertexBallImage src f₁ w) {x : E3}
    (hxγ : x ∈ section34CompactSplitDiskImage srcBd f₁ e)
    (hc : HasPLCurveCrossingOnAt (frontier (⋃ v, section34CompactVertexBallImage src f₁ v))
      J (section34CompactSplitDiskImage srcBd f₁ e) x) : x ∉ A \ {α 0, α 1} := by
  intro hx
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  have hV : ∀ v, IsPLBall 3 (section34CompactVertexBallImage src f₁ v) :=
    fun v => (hcut.isPLCellOn_vertexBallImage hf₁ v).isPLBall_three
  have hxE := (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset hxγ
  have hwe := hcut.subset_of_mem_splitDiskImage hf₁ hxE (hAV hx.1)
  obtain ⟨u, _, hends, heq⟩ : ∃ u : Section34CompactVertexIndex K K', w ≠ u ∧
      (e.1 : Set E3) = (w.1 : Set E3) ∪ (u.1 : Set E3) ∧
      section34CompactSplitDiskImage src f₁ e = section34CompactVertexBallImage src f₁ w ∩
        section34CompactVertexBallImage src f₁ u := by
    obtain ⟨a, b, hab, heab, heq⟩ := hcut.splitDiskImage_eq_inter hf₁ e
    rcases eq_or_eq_of_section34CompactVertexIndex_subset e heab hwe with rfl | rfl
    · exact ⟨b, hab, heab, heq⟩
    · exact ⟨a, hab.symm, heab.trans (union_comm _ _), heq.trans (inter_comm _ _)⟩
  have hlocal := eventually_mem_frontier_iUnion_iff_pair
    (fun v => (hV v).isPolyhedron.isClosed) (i := w) (j := u) (x := x) (by
      intro v hvw hvu hxv
      rcases eq_or_eq_of_section34CompactVertexIndex_subset e hends
        (hcut.subset_of_mem_splitDiskImage hf₁ hxE hxv) with hv | hv
      · exact hvw hv
      · exact hvu hv)
  have hlocalA := hc.swap.eventually_mem_arc_iff hα hAJ hx
  obtain ⟨q, hq, hqb⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
  have hq' : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      (section34CompactVertexBallImage src f₁ w ∩ section34CompactVertexBallImage src f₁ u) :=
    heq ▸ hq
  have hDU : section34CompactVertexBallImage src f₁ w ∩
      section34CompactVertexBallImage src f₁ u ⊆
        frontier (section34CompactVertexBallImage src f₁ u) := by
    have hD : IsPLBall 2 (section34CompactVertexBallImage src f₁ u ∩
        section34CompactVertexBallImage src f₁ w) := by
      rw [inter_comm]
      exact ⟨q, hq'⟩
    rw [inter_comm]
    exact (hV w).inter_subset_frontier_of_isPLBall hD (by decide)
  have hc' := hc.congr hlocal (by filter_upwards [hlocalA] with y hy using hy.symm)
    (Filter.Eventually.of_forall fun y => by rw [hqb])
  exact hc'.not_subset_of_ball_seam (hV w).isPolyhedron.isClosed
    (hV u).isPolyhedron.isClosed (hV u).isPLSphere_frontier hq' hDU hAV

theorem Section34CompactCutFrame.ne_initial_points_of_arcs_in_vertex_ball
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (w : Section34CompactVertexIndex K K') (e : Section34CompactEdgeIndex K K')
    {J A B : Set E3} {α β : ℝ → E3}
    (hα : IsPLHomeomorphOn α (Icc 0 1) A) (hβ : IsPLHomeomorphOn β (Icc 0 1) B)
    (hAJ : A ⊆ J) (hBJ : B ⊆ J)
    (hAV : A ⊆ section34CompactVertexBallImage src f₁ w)
    (hBV : B ⊆ section34CompactVertexBallImage src f₁ w)
    (hAB : A ∩ B ⊆ {α 0, α 1})
    (hxγ : α 0 ∈ section34CompactSplitDiskImage srcBd f₁ e)
    (hc : HasPLCurveCrossingOnAt (frontier (⋃ v, section34CompactVertexBallImage src f₁ v))
      J (section34CompactSplitDiskImage srcBd f₁ e) (α 0)) : α 0 ≠ β 0 := by
  intro hp
  have ha : IsPLHomeomorphOn (fun t => α ((1 / 2 : ℝ) * t)) (Icc 0 1) (α '' Icc 0 (1 / 2)) := by
    simpa only [sub_zero, add_zero] using isPLHomeomorphOn_comp_mul_add_Icc hα
      (a := 0) (b := 1 / 2) le_rfl (by norm_num) (by norm_num)
  have hb : IsPLHomeomorphOn (fun t => β ((1 / 2 : ℝ) * t)) (Icc 0 1) (β '' Icc 0 (1 / 2)) := by
    simpa only [sub_zero, add_zero] using isPLHomeomorphOn_comp_mul_add_Icc hβ
      (a := 0) (b := 1 / 2) le_rfl (by norm_num) (by norm_num)
  have hasub : α '' Icc 0 (1 / 2) ⊆ A :=
    (image_mono (Icc_subset_Icc le_rfl (by norm_num))).trans hα.image_eq.subset
  have hbsub : β '' Icc 0 (1 / 2) ⊆ B :=
    (image_mono (Icc_subset_Icc le_rfl (by norm_num))).trans hβ.image_eq.subset
  have hinter : α '' Icc 0 (1 / 2) ∩ β '' Icc 0 (1 / 2) = {α 0} := by
    apply Subset.antisymm
    · rintro x ⟨hxA, hxB⟩
      rcases hAB ⟨hasub hxA, hbsub hxB⟩ with h0 | h1
      · exact h0
      · obtain ⟨t, ht, htx⟩ := hxA
        have ht1 : t = 1 := hα.bijOn.injOn ⟨ht.1, ht.2.trans (by norm_num)⟩
          (by norm_num) (htx.trans h1)
        norm_num [ht1] at ht
    · rintro x rfl
      exact ⟨⟨0, by norm_num, rfl⟩, ⟨0, by norm_num, hp.symm⟩⟩
  obtain ⟨γ, hγ, _, hγmid, _⟩ := exists_isPLHomeomorphOn_Icc_concat
    (isPLHomeomorphOn_comp_one_sub ha) hb (by simpa only [mul_zero, sub_self] using hp.symm)
    (by simpa only [sub_self, mul_zero] using hinter)
  have hmid : γ (1 / 2) = α 0 := by simpa only [sub_self, mul_zero] using hγmid
  have hxC : α 0 ∈ (α '' Icc 0 (1 / 2) ∪ β '' Icc 0 (1 / 2)) \ {γ 0, γ 1} := by
    refine ⟨hmid ▸ hγ.bijOn.mapsTo (by norm_num), ?_⟩
    rintro (h0 | h1)
    · have hm0 := hγ.bijOn.injOn (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
        (by norm_num) (hmid.trans h0)
      norm_num at hm0
    · have hm1 := hγ.bijOn.injOn (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
        (by norm_num) (hmid.trans h1)
      norm_num at hm1
  exact hcut.not_arc_interior_on_split_disk_boundary hf₁ w e hγ
    (union_subset (hasub.trans hAJ) (hbsub.trans hBJ))
    (union_subset (hasub.trans hAV) (hbsub.trans hBV)) hxγ hc hxC

end DifferentialGeometry.Topology.PiecewiseLinear
