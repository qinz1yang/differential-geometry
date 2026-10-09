/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactInnermostReturn
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSeparatingReturn

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}
  {H : Finset E3 → Set E3}
  {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem exists_admissible_operation_of_separating_trace
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34CompactSimplexIndex K 3) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJcomp : J ∈ section34CompactTraceComponents
      (section34CompactVertexBallImage src f₁) fblBd s)
    (hsep : ¬ IsPreconnected
      (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) \ J)) :
    ∃ t : Section34CompactSimplexIndex K 3,
      Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
        (section34CompactSplitDiskImage src f₁) fbl fblBd t ∨
      Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
        (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fblBd t := by
  classical
  by_cases hcomp : ∃ t, Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁) fbl fblBd t
  · obtain ⟨t, ht⟩ := hcomp
    exact ⟨t, Or.inl ht⟩
  have hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t :=
    fun t ht => hcomp ⟨t, ht⟩
  have hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) := by
    obtain ⟨x, _, hxJ⟩ := hJcomp
    rw [← hxJ]
    exact connectedComponentIn_subset _ _
  have hJΘ : J ⊆ frontier
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) :=
    fun x hx => ((hinv.inter_frontier_faceTorus_eq hcut hgraph.2.1 s).symm.subset (hJT hx)).2
  obtain ⟨_, _, _, _, _, _, _, _, hnest, _⟩ := id hgraph
  obtain ⟨_, _, _, _, hT, _⟩ := hnest s
  obtain ⟨Δ, q, hq, hΔT, hqJ⟩ :=
    hT.isPLTorus_frontier.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hJ hJΘ hsep
  have hΔ : IsPLCellOn 2 Δ J := by
    rw [hqJ]
    exact isPLCellOn_id_of_isPLBall hq
  obtain ⟨w, e, B, η, hη, hBJ, hBS, hends, hmeet⟩ :=
    exists_compact_vertex_return_arc_of_torus_disk hcut hgraph hinv hnc s hJ hJcomp hΔ hΔT
  obtain ⟨t, ht⟩ := exists_admissible_bigon_of_returning_arc hinv hcut hgraph hnc s w e hη
    (fun x hx => (hJT (hBJ hx)).1) hBS hends hmeet
  exact ⟨t, Or.inr ht⟩

theorem Section34CompactFaceBallInvariants.trace_circle_nonseparating_of_no_operation
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (hnb : ∀ t, ¬ Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd t)
    (s : Section34CompactSimplexIndex K 3) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJcomp : J ∈ section34CompactTraceComponents
      (section34CompactVertexBallImage src f₁) fblBd s) :
    IsPreconnected
      (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) \ J) := by
  by_contra hsep
  obtain ⟨t, ht | ht⟩ :=
    exists_admissible_operation_of_separating_trace hcut hgraph hinv s hJ hJcomp hsep
  · exact hnc t ht
  · exact hnb t ht

end DifferentialGeometry.Topology.PiecewiseLinear
