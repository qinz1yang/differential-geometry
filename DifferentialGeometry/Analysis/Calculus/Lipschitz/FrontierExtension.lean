import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Positivity

section

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis

private theorem exists_frontier_mem_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {x y : E} (hx : x ∈ U) (hy : y ∉ U) :
    ∃ q, q ∈ segment ℝ x y ∧ q ∈ frontier U := by
  by_contra h
  have hfront : ∀ q ∈ segment ℝ x y, q ∉ frontier U := by
    simpa only [not_exists, not_and] using h
  have hclosure : closure U ∩ segment ℝ x y ⊆ U := by
    intro q hq
    by_contra hqU
    exact hfront q hq.2 (by simpa only [frontier, hU.interior_eq, mem_sdiff] using ⟨hq.1, hqU⟩)
  have hsub := (convex_segment x y).isPreconnected.subset_of_closure_inter_subset hU
    ⟨x, left_mem_segment ℝ x y, hx⟩ hclosure
  exact hy (hsub (right_mem_segment ℝ x y))

open Classical in
theorem _root_.LipschitzOnWith.piecewise_const_of_eq_on_frontier
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace F]
    {U K : Set E} {f : E → F} {c : F} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (closure U ∩ K)) (hU : IsOpen U) (hK : Convex ℝ K)
    (hfront : ∀ q ∈ frontier U ∩ K, f q = c) :
    LipschitzOnWith L (U.piecewise f (fun _ => c)) K := by
  classical
  have hcross {x y : E} (hx : x ∈ K) (hy : y ∈ K) (hxU : x ∈ U) (hyU : y ∉ U) :
      dist (f x) c ≤ L * dist x y := by
    obtain ⟨q, hqseg, hqfront⟩ := exists_frontier_mem_segment hU hxU hyU
    have hqK : q ∈ K := hK.segment_subset hx hy hqseg
    have hdist : dist x q ≤ dist x y := by
      have hh := segment_subset_closedBall_left x y hqseg
      simpa only [Metric.mem_closedBall, dist_comm q x] using hh
    rw [← hfront q ⟨hqfront, hqK⟩]
    exact (hf.dist_le_mul x ⟨subset_closure hxU, hx⟩ q
      ⟨frontier_subset_closure hqfront, hqK⟩).trans
      (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxU : x ∈ U
  · by_cases hyU : y ∈ U
    · rw [piecewise_eq_of_mem U f (fun _ => c) hxU,
        piecewise_eq_of_mem U f (fun _ => c) hyU]
      exact hf.dist_le_mul x ⟨subset_closure hxU, hx⟩ y ⟨subset_closure hyU, hy⟩
    · rw [piecewise_eq_of_mem U f (fun _ => c) hxU,
        piecewise_eq_of_notMem U f (fun _ => c) hyU]
      exact hcross hx hy hxU hyU
  · by_cases hyU : y ∈ U
    · rw [piecewise_eq_of_notMem U f (fun _ => c) hxU,
        piecewise_eq_of_mem U f (fun _ => c) hyU, dist_comm]
      simpa only [dist_comm y x] using hcross hy hx hyU hxU
    · rw [piecewise_eq_of_notMem U f (fun _ => c) hxU,
        piecewise_eq_of_notMem U f (fun _ => c) hyU, dist_self]
      positivity

open Classical in
theorem _root_.LipschitzOnWith.piecewise_sub_const_of_eq_on_frontier
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    {U K : Set E} {f : E → F} {c : F} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (closure U ∩ K)) (hU : IsOpen U) (hK : Convex ℝ K)
    (hfront : ∀ q ∈ frontier U ∩ K, f q = c) :
    LipschitzOnWith L (U.piecewise (fun x => f x - c) (fun _ => 0)) K := by
  classical
  have hsub : LipschitzOnWith L (fun x => f x - c) (closure U ∩ K) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_sub_right] using hf.dist_le_mul x hx y hy
  exact hsub.piecewise_const_of_eq_on_frontier hU hK (fun q hq => by rw [hfront q hq, sub_self])

open Classical in
theorem _root_.LipschitzOnWith.piecewise_sub_const_on_ball_of_eq_on_frontier
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    {U : Set E} {f : E → F} {c : F} {L : ℝ≥0} {p : E} {R : ℝ}
    (hf : LipschitzOnWith L f (closure U ∩ Metric.ball p R)) (hU : IsOpen U)
    (hfront : ∀ q ∈ frontier U ∩ Metric.ball p R, f q = c) :
    LipschitzOnWith L (U.piecewise (fun x => f x - c) (fun _ => 0)) (Metric.ball p R) :=
  hf.piecewise_sub_const_of_eq_on_frontier hU (convex_ball p R) hfront

end DifferentialGeometry.Analysis

end

end
