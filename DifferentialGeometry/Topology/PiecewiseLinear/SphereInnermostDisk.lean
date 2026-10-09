/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphereSchoenflies

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_innermost_disk {S : Set E} (hS : IsPLSphere 2 S) {ι : Type*}
    [Finite ι] [Nonempty ι] {J : ι → Set E} (hJ : ∀ i, IsPLSphere 1 (J i))
    (hJS : ∀ i, J i ⊆ S) (hdisj : Pairwise fun i j => Disjoint (J i) (J j)) :
    ∃ (i : ι) (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ S ∧ q '' stdSimplexBoundary 2 = J i ∧
        ∀ j, j ≠ i → Disjoint D (J j) := by
  classical
  have hside : ∀ {D Y : Set E} {q : (Fin 3 → ℝ) → E} {i : ι},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D → D ⊆ S → q '' stdSimplexBoundary 2 = J i →
      IsPreconnected Y → Y ⊆ S → Disjoint Y (J i) → Y ⊆ D ∨ Disjoint D Y := by
    intro D Y q i hq hDS hqJ hY hYS hYJ
    have hD : IsPLBall 2 D := ⟨q, hq⟩
    have hmeet : D ∩ closure (S \ D) = J i := by
      rw [hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDS, hqJ]
    have hcover : Y ⊆ D ∪ closure (S \ D) := fun y hy => by
      by_cases hyD : y ∈ D
      · exact Or.inl hyD
      · exact Or.inr (subset_closure ⟨hYS hy, hyD⟩)
    have hdis : Y ∩ (D ∩ closure (S \ D)) = ∅ := by
      rw [hmeet]
      exact hYJ.inter_eq
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hY D (closure (S \ D))
      hD.isPolyhedron.isClosed isClosed_closure hcover hdis with h | h
    · exact Or.inl h
    · refine Or.inr (Set.disjoint_left.mpr fun y hyD hyY => ?_)
      have hy : y ∈ D ∩ closure (S \ D) := ⟨hyD, h hyY⟩
      rw [hmeet] at hy
      exact Set.disjoint_left.mp hYJ hyY hy
  have hex : ∃ n, ∃ (i : ι) (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ S ∧ q '' stdSimplexBoundary 2 = J i ∧
        {j | j ≠ i ∧ J j ⊆ D}.ncard = n := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    obtain ⟨D₀, _, q₀, _, hq₀, -, hq₀J, -, hcover, -⟩ :=
      exists_isPLBall_pair_of_isPLSphere_two hS (hJ i₀) (hJS i₀)
    exact ⟨_, i₀, D₀, q₀, hq₀, subset_union_left.trans hcover.subset, hq₀J, rfl⟩
  obtain ⟨i, D, q, hq, hDS, hqJ, hn⟩ := Nat.find_spec hex
  have hnone : ∀ j, j ≠ i → ¬ J j ⊆ D := by
    intro j hji hjD
    obtain ⟨Q, q', hq', hQS, hQi, hq'J⟩ :=
      hS.exists_isPLBall_with_boundary_disjoint_of_isPreconnected
        (hJ i).isConnected.isPreconnected (hJS i) (hJ j) (hJS j) (hdisj (Ne.symm hji))
    have hjQ : J j ⊆ Q := by
      rw [← hq'J, ← hq'.image_eq]
      exact image_mono fun x hx => hx.1
    obtain ⟨x, hx⟩ := (hJ j).nonempty
    have hQD : Q ⊆ D := by
      rcases hside hq hDS hqJ (show IsPLBall 2 Q from ⟨q', hq'⟩).isConnected.isPreconnected
        hQS hQi.symm with h | h
      · exact h
      · exact (Set.disjoint_left.mp h (hjD hx) (hjQ hx)).elim
    have hlt : {k | k ≠ j ∧ J k ⊆ Q}.ncard < {k | k ≠ i ∧ J k ⊆ D}.ncard := by
      refine Set.ncard_lt_ncard (ssubset_of_subset_not_subset
        (fun k hk => ⟨fun hki => ?_, hk.2.trans hQD⟩) fun hsub => ?_)
      · obtain ⟨y, hy⟩ := (hJ k).nonempty
        subst hki
        exact Set.disjoint_left.mp hQi hy (hk.2 hy)
      · exact (hsub ⟨hji, hjD⟩).1 rfl
    have hmin := Nat.find_min' hex ⟨j, Q, q', hq', hQS, hq'J, rfl⟩
    omega
  refine ⟨i, D, q, hq, hDS, hqJ, fun j hji => ?_⟩
  rcases hside hq hDS hqJ (hJ j).isConnected.isPreconnected (hJS j) (hdisj hji) with h | h
  · exact absurd h (hnone j hji)
  · exact h

end DifferentialGeometry.Topology.PiecewiseLinear
