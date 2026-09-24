import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Normed.Module.Convex

section

open Set Metric

namespace DifferentialGeometry.Analysis

theorem ball_infDist_frontier_subset_of_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (hfrontier : (frontier U).Nonempty) :
    ball x (infDist x (frontier U)) ⊆ U := by
  let V := ball x (infDist x (frontier U))
  have hxn : x ∉ frontier U := by
    rw [hU.frontier_eq]
    exact fun h => h.2 hx
  have hd : 0 < infDist x (frontier U) :=
    (isClosed_frontier.notMem_iff_infDist_pos hfrontier).mp hxn
  have hdis : Disjoint (frontier U) V := (disjoint_ball_infDist (x := x) (s := frontier U)).symm
  let _ : PreconnectedSpace V :=
    Subtype.preconnectedSpace (convex_ball x (infDist x (frontier U))).isPreconnected
  have hc : IsClopen (Subtype.val ⁻¹' U : Set V) := isClopen_preimage_val hU hdis
  have he : (Subtype.val ⁻¹' U : Set V) = univ := hc.eq_univ ⟨⟨x, mem_ball_self hd⟩, hx⟩
  intro y hy
  have hmem : (⟨y, hy⟩ : V) ∈ (Subtype.val ⁻¹' U : Set V) := he ▸ mem_univ _
  exact hmem

end DifferentialGeometry.Analysis

end
