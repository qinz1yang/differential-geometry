/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.MetricSpace.Pseudo.Basic

open Set Topology

namespace Metric

theorem exists_pairwise_disjoint_closedBall_of_isDiscrete
    {X ι : Type*} [PseudoMetricSpace X] {p : ι → X} (hp : Function.Injective p)
    (hdiscrete : IsDiscrete (range p)) {N : ι → Set X} (hN : ∀ i, N i ∈ 𝓝 (p i))
    {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i) :
    ∃ r : ι → ℝ, (∀ i, 0 < r i ∧ r i < δ i ∧ closedBall (p i) (r i) ⊆ N i) ∧
      Pairwise fun i j => Disjoint (closedBall (p i) (r i)) (closedBall (p j) (r j)) := by
  choose R hR hsingle using fun i =>
    exists_closedBall_inter_eq_singleton_of_discrete hdiscrete (mem_range_self i)
  choose S hS hSN using fun i => mem_nhds_iff.mp (hN i)
  let r (i : ι) := min (R i / 3) (min (S i / 2) (δ i / 2))
  have hrR (i : ι) : r i ≤ R i / 3 := min_le_left _ _
  have hrS (i : ι) : r i ≤ S i / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ (i : ι) : r i ≤ δ i / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsep (i j : ι) (hij : i ≠ j) : R i < dist (p i) (p j) := by
    by_contra hnot
    have hmem : p j ∈ closedBall (p i) (R i) ∩ range p :=
      ⟨by rw [mem_closedBall, dist_comm]; exact not_lt.mp hnot, mem_range_self j⟩
    have heq : p j = p i := (hsingle i).subset hmem
    exact hij (hp heq.symm)
  refine ⟨r, fun i => ⟨lt_min (div_pos (hR i) (by norm_num))
    (lt_min (half_pos (hS i)) (half_pos (hδ i))), (hrδ i).trans_lt (half_lt_self (hδ i)),
    (closedBall_subset_ball ((hrS i).trans_lt (half_lt_self (hS i)))).trans (hSN i)⟩, ?_⟩
  intro i j hij
  apply closedBall_disjoint_closedBall
  have hsep₁ := hsep i j hij
  have hsep₂ := hsep j i hij.symm
  rw [dist_comm (p j) (p i)] at hsep₂
  linarith [hrR i, hrR j, hR i]

end Metric
