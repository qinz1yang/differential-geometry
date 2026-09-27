/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.FinitePartition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBoundarySurface
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSeamArcSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceFamily
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVertexOperations

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}
  {H : Finset E3 → Set E3}
  {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem exists_compact_trace_crosscut_in_return_disk
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fbl fblBd)
    (hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (s : Section34CompactSimplexIndex K 3)
    (w : Section34CompactVertexIndex K K')
    (e : Section34CompactEdgeIndex K K')
    {B R D : Set E3} {η δ : ℝ → E3}
    (hη : IsPLHomeomorphOn η (Icc 0 1) B)
    (hBP : B ⊆ fblBd s)
    (hBS : B ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hends : ({η 0, η 1} : Set E3) ⊆
      section34CompactSplitDiskImage srcBd f₁ e)
    (hmeet : B ∩ (⋃ e' : Section34CompactEdgeIndex K K',
      section34CompactSplitDiskImage src f₁ e') = {η 0, η 1})
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) R)
    (hδ0 : δ 0 = η 0) (hδ1 : δ 1 = η 1)
    (hR : R ⊆ section34CompactSplitDiskImage srcBd f₁ e)
    (hBR : B ∩ R = {η 0, η 1})
    (hD : IsPLCellOn 2 D (B ∪ R))
    (hDloc : D ⊆ section34CompactVertexBallImage srcBd f₁ w ∩
      frontier (⋃ v : Section34CompactVertexIndex K K',
        section34CompactVertexBallImage src f₁ v))
    (hDE : D ∩ section34CompactSplitDiskImage src f₁ e = R)
    (hother : ∀ e' : Section34CompactEdgeIndex K K', e' ≠ e →
      Disjoint D (section34CompactSplitDiskImage src f₁ e'))
    (hdirty : ((D \ (B ∪ R)) ∩
      (⋃ t : Section34CompactSimplexIndex K 3, fblBd t)).Nonempty) :
    ∃ (t : Section34CompactSimplexIndex K 3) (A : Set E3) (α : ℝ → E3),
      IsPLHomeomorphOn α (Icc 0 1) A ∧
      A ⊆ fblBd t ∧ A ⊆ D ∧
      A ∩ (B ∪ R) = {α 0, α 1} ∧
      ({α 0, α 1} : Set E3) ⊆ R \ {η 0, η 1} := by
  classical
  have hf₁ := hgraph.2.1
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  obtain ⟨q, hq, hqB⟩ := hD.exists_isPLHomeomorphOn_stdSimplex
  have hBN : B ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v) :=
    fun x hx => (hDloc (hD.boundary_subset (Or.inl hx))).2
  obtain ⟨ι, hι, label, F, hF, hdis, htrace⟩ :=
    exists_finite_labelled_compact_trace_circles hcut hf₁ hinv
  have : Finite ι := hι
  have hBU : B ⊆ ⋃ i, F i := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp ((htrace s).subset ⟨hBP hx, hBN hx⟩)
    exact mem_iUnion.mpr ⟨i, hxi⟩
  have hpair : (range F).PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hdis (fun heq => hij (congrArg F heq))
  obtain ⟨G, ⟨hGF, hBG⟩, _⟩ :=
    existsUnique_subset_of_isConnected_of_finite_closed_partition
      (((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hη).isConnected)
      (finite_range F) (by rintro _ ⟨i, rfl⟩; exact (hF i).1.isPolyhedron.isClosed) hpair
      (by simpa only [sUnion_range] using hBU)
  obtain ⟨i₀, rfl⟩ := hGF
  obtain ⟨x, hxD, hxP⟩ := hdirty
  obtain ⟨t, hxt⟩ := mem_iUnion.mp hxP
  obtain ⟨j, _, hxj⟩ := mem_iUnion₂.mp ((htrace t).subset ⟨hxt, (hDloc hxD.1).2⟩)
  have hjno : ¬ F j ⊆ D := by
    intro hjD
    exact hinv.not_circle_subset_vertexBall_of_no_compression hcut hgraph hnc (label j) w
      (hF j).1 (fun y hy => ((hF j).2 hy).1) (fun y hy => ((hF j).2 hy).2)
      (hjD.trans (fun y hy => hV.boundary_subset (hDloc hy).1))
  have hrel : Disjoint (F j) B ∨ B ⊆ F j := by
    by_cases hji : j = i₀
    · exact Or.inr (hji.symm ▸ hBG)
    · exact Or.inl ((hdis hji).mono_right hBG)
  obtain ⟨_, _, _, _, _, _, _, hfinite, _⟩ := id hinv
  have hDall : D ∩ (⋃ d, section34CompactSplitDiskImage src f₁ d) = R := by
    apply Subset.antisymm
    · rintro y ⟨hyD, hyE⟩
      obtain ⟨d, hyd⟩ := mem_iUnion.mp hyE
      by_cases hde : d = e
      · exact hDE.subset ⟨hyD, hde ▸ hyd⟩
      · exact (Set.disjoint_left.mp (hother d hde) hyD hyd).elim
    · intro y hy
      have hyDE := hDE.symm.subset hy
      exact ⟨hyDE.1, mem_iUnion.mpr ⟨e, hyDE.2⟩⟩
  have hjfin : (F j ∩ R).Finite := (hfinite (label j)).subset (by
    rintro y ⟨hyF, hyR⟩
    obtain ⟨hyD, hyE⟩ := hDall.symm.subset hyR
    obtain ⟨d, hyd⟩ := mem_iUnion.mp hyE
    have hyγ : y ∈ section34CompactSplitDiskImage srcBd f₁ d := by
      by_contra hyγ
      exact (hDloc hyD).2.2 (hcut.splitDiskImage_sdiff_subset_interior hf₁ d ⟨hyd, hyγ⟩)
    exact ⟨((hF j).2 hyF).1, mem_iUnion.mpr ⟨d, hyγ⟩⟩)
  have hboundary : D ∩ closure
      (frontier (⋃ v, section34CompactVertexBallImage src f₁ v) \ D) = B ∪ R :=
    (hcut.inter_closure_sdiff_disk_on_frontier hf₁ hq (fun y hy => (hDloc hy).2)).trans hqB.symm
  obtain ⟨A, α, hα, hAFD, hα0R, hα1R, _, hopen, _⟩ :=
    exists_crossing_subarc_ending_on_boundary_arc (hF j).1 (fun y hy => ((hF j).2 hy).2)
      hD.isCompact.isClosed hboundary hη hBR hrel hjfin hjno ⟨hxj, hxD⟩
  have hAL : A ∩ (B ∪ R) = {α 0, α 1} := by
    apply Subset.antisymm
    · rintro y ⟨hyA, hyL⟩
      by_contra hy
      exact (hopen ⟨hyA, hy⟩).2 hyL
    · intro y hy
      exact ⟨(pair_subset (hα.bijOn.mapsTo (by norm_num))
        (hα.bijOn.mapsTo (by norm_num))) hy, Or.inr ((pair_subset hα0R hα1R) hy)⟩
  have hcorner : ∀ γ : ℝ → E3, IsPLHomeomorphOn γ (Icc 0 1) A →
      ({γ 0, γ 1} : Set E3) = {α 0, α 1} → γ 0 ∉ ({η 0, η 1} : Set E3) := by
    intro γ hγ hγends hp
    have hpA : γ 0 ∈ A := hγ.bijOn.mapsTo (by norm_num)
    have hpF : γ 0 ∈ F j := (hAFD hpA).1
    have hpB : γ 0 ∈ B := (pair_subset (hη.bijOn.mapsTo (by norm_num))
      (hη.bijOn.mapsTo (by norm_num))) hp
    have hBFj : B ⊆ F j := hrel.resolve_left fun hd => Set.disjoint_left.mp hd hpF hpB
    have hpE := (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset (hends hp)
    have hpOld := hmeet.subset ⟨hpB, mem_iUnion.mpr ⟨e, hpE⟩⟩
    have hpR : γ 0 ∈ R := by
      rw [← hδ0, ← hδ1] at hpOld
      exact (pair_subset (hδ.bijOn.mapsTo (by norm_num))
        (hδ.bijOn.mapsTo (by norm_num))) hpOld
    have hpγ := hR hpR
    have hc := hinv.curve_crossing_trace_circle hcut hf₁ (label j) (hF j).1 (hF j).2 e
      ⟨hpF, hpγ⟩
    have hAB : A ∩ B ⊆ {γ 0, γ 1} :=
      fun y hy => hγends.symm.subset (hAL.subset ⟨hy.1, Or.inl hy.2⟩)
    have hAV : A ⊆ section34CompactVertexBallImage src f₁ w :=
      fun y hy => hV.boundary_subset (hDloc (hAFD hy).2).1
    have hBV : B ⊆ section34CompactVertexBallImage src f₁ w := hBS.trans hV.boundary_subset
    rcases hp with hp0 | hp1
    · exact hcut.ne_initial_points_of_arcs_in_vertex_ball hf₁ w e hγ hη
        (fun y hy => (hAFD hy).1) hBFj hAV hBV hAB hpγ hc hp0
    · have hrev := isPLHomeomorphOn_comp_one_sub hη
      exact hcut.ne_initial_points_of_arcs_in_vertex_ball hf₁ w e hγ hrev
        (fun y hy => (hAFD hy).1) hBFj hAV hBV hAB hpγ hc
        (by simpa only [sub_zero, mem_singleton_iff] using hp1)
  have h0 := hcorner α hα rfl
  have h1 : α 1 ∉ ({η 0, η 1} : Set E3) := by
    have hr := hcorner (fun t => α (1 - t)) (isPLHomeomorphOn_comp_one_sub hα)
      (by simp only [sub_zero, sub_self, pair_comm])
    simpa only [sub_zero] using hr
  refine ⟨label j, A, α, hα, fun y hy => ((hF j).2 (hAFD hy).1).1,
    fun y hy => (hAFD hy).2, hAL, ?_⟩
  exact pair_subset ⟨hα0R, h0⟩ ⟨hα1R, h1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
