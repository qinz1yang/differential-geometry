/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcSubinterval
import DifferentialGeometry.Topology.PiecewiseLinear.CircleClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactReturnDiskDescent
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactReturnDisks
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskContainment

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem exists_admissible_bigon_of_returning_arc
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hnc : ∀ t : Section34CompactSimplexIndex K 3,
      ¬ Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
        (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    (e₀ : Section34CompactEdgeIndex K K') {B₀ : Set E3} {η : ℝ → E3}
    (hη : IsPLHomeomorphOn η (Icc 0 1) B₀) (hBP : B₀ ⊆ fblBd s)
    (hBS : B₀ ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hends : ({η 0, η 1} : Set E3) ⊆ section34CompactSplitDiskImage srcBd f₁ e₀)
    (hmeet : B₀ ∩ (⋃ e, section34CompactSplitDiskImage src f₁ e) = {η 0, η 1}) :
    ∃ t : Section34CompactSimplexIndex K 3,
      Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
        (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fblBd t := by
  classical
  have hf₁ := hgraph.2.1
  have := finite_section34CompactSimplexIndex hcut.2.1 3
  let F := ⋃ t : Section34CompactSimplexIndex K 3, fblBd t
  let P := fun (t : Section34CompactSimplexIndex K 3) (v : Section34CompactVertexIndex K K')
      (e : Section34CompactEdgeIndex K K') (B R D : Set E3) (q : (Fin 3 → ℝ) → E3)
      (β δ : ℝ → E3) =>
    IsPLHomeomorphOn β (Icc 0 1) B ∧ B ⊆ fblBd t ∧
      B ⊆ section34CompactVertexBallImage srcBd f₁ v ∧
      ({β 0, β 1} : Set E3) ⊆ section34CompactSplitDiskImage srcBd f₁ e ∧
      B ∩ (⋃ d, section34CompactSplitDiskImage src f₁ d) = {β 0, β 1} ∧
      IsPLHomeomorphOn δ (Icc 0 1) R ∧ δ 0 = β 0 ∧ δ 1 = β 1 ∧
      R ⊆ section34CompactSplitDiskImage srcBd f₁ e ∧ B ∩ R = {β 0, β 1} ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ q '' stdSimplexBoundary 2 = B ∪ R ∧
      D ⊆ section34CompactVertexBallImage srcBd f₁ v ∩
        frontier (⋃ u, section34CompactVertexBallImage src f₁ u) ∧
      D ∩ section34CompactSplitDiskImage src f₁ e = R ∧
      ∀ d : Section34CompactEdgeIndex K K', d ≠ e →
        Disjoint D (section34CompactSplitDiskImage src f₁ d)
  obtain ⟨R₀, D₀, q₀, δ₀, hδ₀, hδ₀0, hδ₀1, hR₀γ, hB₀R₀, hq₀, hq₀B, hD₀, hD₀E, hforeign⟩ :=
    exists_vertex_return_disk_avoiding_split_disks hinv hcut hgraph s w e₀
      hη hBP hBS hends hmeet
  have hinit : P s w e₀ B₀ R₀ D₀ q₀ η δ₀ :=
    ⟨hη, hBP, hBS, hends, hmeet, hδ₀, hδ₀0, hδ₀1, hR₀γ, hB₀R₀,
      hq₀, hq₀B, hD₀, hD₀E, hforeign⟩
  have hex : ∃ n, ∃ (t : Section34CompactSimplexIndex K 3) (v : Section34CompactVertexIndex K K')
      (e : Section34CompactEdgeIndex K K') (B R D : Set E3) (q : (Fin 3 → ℝ) → E3)
      (β δ : ℝ → E3), P t v e B R D q β δ ∧ (R ∩ F).ncard = n :=
    ⟨_, s, w, e₀, B₀, R₀, D₀, q₀, η, δ₀, hinit, rfl⟩
  obtain ⟨t, v, e, B, R, D, q, β, δ, hdata, hn⟩ := Nat.find_spec hex
  obtain ⟨hβ, hBP', hBV, hends', hBE, hδ, hδ0, hδ1, hRγ, hBR,
    hq, hqB, hDloc, hDE, hother⟩ := hdata
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ v
  have hE := hcut.isPLCellOn_splitDiskImage hf₁ e
  have hDcell : IsPLCellOn 2 D (B ∪ R) := by
    rw [← hqB]
    exact isPLCellOn_id_of_isPLBall hq
  have hRcell : IsPLCellOn 1 R {β 0, β 1} := by
    rw [← hδ0, ← hδ1]
    exact isPLCellOn_one_of_isPLHomeomorphOn_Icc hδ
  refine ⟨t, v, e, B, R, {β 0, β 1}, D, B ∪ R,
    isPLCellOn_one_of_isPLHomeomorphOn_Icc hβ, hBP', hBV, hends', hBE, hRcell,
    hRγ, hBR, hDcell, hDloc, rfl, ?_⟩
  intro u
  apply Set.disjoint_left.mpr
  intro x hxD hxP
  have hdirty : ((D \ (B ∪ R)) ∩ ⋃ a : Section34CompactSimplexIndex K 3, fblBd a).Nonempty :=
    ⟨x, hxD, mem_iUnion.mpr ⟨u, hxP⟩⟩
  obtain ⟨a, A, α, hα, hAP, hAD, hAL, hαends⟩ :=
    exists_compact_trace_crosscut_in_return_disk hcut hgraph hinv hnc t v e
      hβ hBP' hBV hends' hBE hδ hδ0 hδ1 hRγ hBR hDcell hDloc hDE hother hdirty
  have hαne : α 0 ≠ α 1 := fun heq => zero_ne_one
    (hα.bijOn.injOn (by norm_num) (by norm_num) heq)
  have hαR : ({α 0, α 1} : Set E3) ⊆ R \ {δ 0, δ 1} := by
    simpa only [hδ0, hδ1] using hαends
  obtain ⟨R', δ', hδ', hδ'0, hδ'1, hR'⟩ :=
    exists_subarc_between_interior_points hδ (hαR (by simp)) (hαR (by simp)) hαne
  rw [hδ0, hδ1] at hR'
  have hR'R : R' ⊆ R := hR'.trans sdiff_subset
  have hendsR' : ({α 0, α 1} : Set E3) ⊆ R' := by
    rw [← hδ'0, ← hδ'1]
    exact pair_subset (hδ'.bijOn.mapsTo (by norm_num)) (hδ'.bijOn.mapsTo (by norm_num))
  have hS : IsPLSphere 2 (section34CompactVertexBallImage srcBd f₁ v) := by
    rw [hV.boundary_eq_frontier]
    exact hV.isPLBall_three.isPLSphere_frontier
  obtain ⟨D', q', hq', hD'D, hq'A, hD'J⟩ :=
    hS.exists_disk_between_proper_arc_and_boundary_arc hq (fun y hy => (hDloc hy).1)
      hα hδ' hδ'0 hδ'1 hAD
      (hR'R.trans (subset_union_right.trans hqB.symm.subset)) (by rw [hqB]; exact hAL)
  rw [hqB] at hD'J
  have hD'R : D' ∩ R = R' := Subset.antisymm
    (fun y hy => hD'J.subset ⟨hy.1, Or.inr hy.2⟩)
    (fun y hy => ⟨(hD'J.symm.subset hy).1, hR'R hy⟩)
  have hD'E : D' ∩ section34CompactSplitDiskImage src f₁ e = R' := Subset.antisymm
    (fun y hy => hD'R.subset ⟨hy.1, hDE.subset ⟨hD'D hy.1, hy.2⟩⟩)
    (fun y hy => ⟨(hD'R.symm.subset hy).1, hE.boundary_subset (hRγ (hR'R hy))⟩)
  have hAD' : A ⊆ D' := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hq'A.symm.subset (Or.inl hy)
    exact hzy ▸ hq'.bijOn.mapsTo hz.1
  have hAR' : A ∩ R' = {α 0, α 1} := Subset.antisymm
    (fun y hy => hAL.subset ⟨hy.1, Or.inr (hR'R hy.2)⟩)
    (fun y hy => ⟨(pair_subset (hα.bijOn.mapsTo (by norm_num))
      (hα.bijOn.mapsTo (by norm_num))) hy, hendsR' hy⟩)
  have hAE : A ∩ (⋃ d, section34CompactSplitDiskImage src f₁ d) = {α 0, α 1} := by
    apply Subset.antisymm
    · rintro y ⟨hyA, hyE⟩
      obtain ⟨d, hyd⟩ := mem_iUnion.mp hyE
      by_cases hde : d = e
      · subst d
        exact hAR'.subset ⟨hyA, hD'E.subset ⟨hAD' hyA, hyd⟩⟩
      · exact (Set.disjoint_left.mp (hother d hde) (hAD hyA) hyd).elim
    · intro y hy
      exact ⟨(pair_subset (hα.bijOn.mapsTo (by norm_num))
        (hα.bijOn.mapsTo (by norm_num))) hy,
        mem_iUnion.mpr ⟨e, hE.boundary_subset (hRγ (hR'R (hendsR' hy)))⟩⟩
  have hnew : P a v e A R' D' q' α δ' :=
    ⟨hα, hAP, fun y hy => (hDloc (hAD hy)).1, hendsR'.trans (hR'R.trans hRγ), hAE,
      hδ', hδ'0, hδ'1, hR'R.trans hRγ, hAR', hq', hq'A, hD'D.trans hDloc, hD'E,
      fun d hd => (hother d hd).mono_left hD'D⟩
  obtain ⟨_, _, _, _, _, _, _, hfinite, _⟩ := id hinv
  have hZ : (⋃ b : Section34CompactSimplexIndex K 3,
      fblBd b ∩ ⋃ d : Section34CompactEdgeIndex K K',
        section34CompactSplitDiskImage srcBd f₁ d).Finite := finite_iUnion hfinite
  have hfin : (R ∩ F).Finite := hZ.subset (by
    rintro y ⟨hyR, hyF⟩
    obtain ⟨b, hyb⟩ := mem_iUnion.mp hyF
    exact mem_iUnion.mpr ⟨b, hyb, mem_iUnion.mpr ⟨e, hRγ hyR⟩⟩)
  have hcorners : ({β 0, β 1} : Set E3) ⊆ R ∩ F := by
    intro y hy
    exact ⟨(hBR.symm.subset hy).2, mem_iUnion.mpr ⟨t, hBP' ((pair_subset
      (hβ.bijOn.mapsTo (by norm_num)) (hβ.bijOn.mapsTo (by norm_num))) hy)⟩⟩
  have hβne : β 0 ≠ β 1 := fun heq => zero_ne_one
    (hβ.bijOn.injOn (by norm_num) (by norm_num) heq)
  have hdrop := Set.ncard_sdiff_add_ncard_of_subset hcorners hfin
  rw [Set.ncard_pair hβne] at hdrop
  have hcount : (R' ∩ F).ncard ≤ ((R ∩ F) \ {β 0, β 1}).ncard :=
    Set.ncard_le_ncard (fun y hy => ⟨⟨hR'R hy.1, hy.2⟩, (hR' hy.1).2⟩) hfin.sdiff
  have hmin := Nat.find_min' hex ⟨a, v, e, A, R', D', q', α, δ', hnew, rfl⟩
  omega

theorem Section34CompactFaceBallInvariants.not_returning_arc_of_no_operation
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hnc : ∀ t : Section34CompactSimplexIndex K 3,
      ¬ Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
        (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (hnb : ∀ t : Section34CompactSimplexIndex K 3,
      ¬ Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
        (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fblBd t)
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    (e₀ : Section34CompactEdgeIndex K K') {B : Set E3} {η : ℝ → E3}
    (hη : IsPLHomeomorphOn η (Icc 0 1) B) (hBP : B ⊆ fblBd s)
    (hBS : B ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hends : ({η 0, η 1} : Set E3) ⊆ section34CompactSplitDiskImage srcBd f₁ e₀) :
    B ∩ (⋃ e, section34CompactSplitDiskImage src f₁ e) ≠ {η 0, η 1} := by
  intro hmeet
  obtain ⟨t, ht⟩ := exists_admissible_bigon_of_returning_arc hinv hcut hgraph hnc
    s w e₀ hη hBP hBS hends hmeet
  exact hnb t ht

end DifferentialGeometry.Topology.PiecewiseLinear
