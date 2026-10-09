/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocalDiskSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskCircleComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_innermost_disk_subset_of_eventually_eq {S T D₀ : Set E}
    (hS : IsPLSphere 2 S) {q₀ : (Fin 3 → ℝ) → E}
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀) (hD₀S : D₀ ⊆ S)
    (hlocal : ∀ x ∈ D₀, ∀ᶠ y in 𝓝 x, y ∈ T ↔ y ∈ S)
    {ι : Type*} [Finite ι] {J : ι → Set E} (hJ : ∀ i, IsPLSphere 1 (J i))
    (hJT : ∀ i, J i ⊆ T) (hdisj : Pairwise fun i j => Disjoint (J i) (J j))
    (i₀ : ι) (hi₀ : q₀ '' stdSimplexBoundary 2 = J i₀) :
    ∃ (i : ι) (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ D₀ ∧
        q '' stdSimplexBoundary 2 = J i ∧ ∀ j, j ≠ i → Disjoint D (J j) := by
  classical
  have hex : ∃ n, ∃ (i : ι) (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ D₀ ∧
        q '' stdSimplexBoundary 2 = J i ∧ {j | j ≠ i ∧ J j ⊆ D}.ncard = n :=
    ⟨_, i₀, D₀, q₀, hq₀, Subset.rfl, hi₀, rfl⟩
  obtain ⟨i, D, q, hq, hDD₀, hqJ, hn⟩ := Nat.find_spec hex
  have hnone : ∀ j, j ≠ i → ¬ J j ⊆ D := by
    intro j hji hjD
    obtain ⟨R, Q, q', -, hq', hcover, hmeet, hq'J, houter⟩ :=
      hq.exists_disk_complement_of_circle (hJ j) hjD (by rw [hqJ]; exact hdisj hji)
    have hQD : Q ⊆ D := subset_union_right.trans hcover.subset
    have hQi : Disjoint (J i) Q := by
      apply Set.disjoint_left.mpr
      intro x hxi hxQ
      have hxR := houter (hqJ.symm ▸ hxi)
      exact Set.disjoint_left.mp (hdisj hji) (hmeet.subset ⟨hxR, hxQ⟩) hxi
    have hlt : {k | k ≠ j ∧ J k ⊆ Q}.ncard < {k | k ≠ i ∧ J k ⊆ D}.ncard := by
      refine Set.ncard_lt_ncard (ssubset_of_subset_not_subset
        (fun k hk => ⟨fun hki => ?_, hk.2.trans hQD⟩) fun hsub => ?_)
      · obtain ⟨y, hy⟩ := (hJ k).nonempty
        subst hki
        exact Set.disjoint_left.mp hQi hy (hk.2 hy)
      · exact (hsub ⟨hji, hjD⟩).1 rfl
    have hmin := Nat.find_min' hex ⟨j, Q, q', hq', hQD.trans hDD₀, hq'J, rfl⟩
    omega
  refine ⟨i, D, q, hq, hDD₀, hqJ, fun j hji => ?_⟩
  have hloc : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ T ↔ y ∈ S :=
    fun x hx => hlocal x (hDD₀ hx)
  rcases hS.subset_or_disjoint_disk_of_eventually_eq hq (hDD₀.trans hD₀S) hloc
      (hJ j).isConnected.isPreconnected (hJT j) (by rw [hqJ]; exact hdisj hji) with h | h
  · exact (hnone j hji h).elim
  · exact h

end DifferentialGeometry.Topology.PiecewiseLinear
