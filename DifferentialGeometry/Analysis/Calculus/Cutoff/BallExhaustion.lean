import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.IsLUB

section

open Filter Set Metric
open scoped ContDiff Topology NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_contDiff_cutoff_sequence_ball (c : E) (R : ℝ) :
    ∃ η : ℕ → E → ℝ,
      (∀ j, ContDiff ℝ ∞ (η j) ∧ HasCompactSupport (η j) ∧
        tsupport (η j) ⊆ ball c R ∧
        (∀ x, 0 ≤ η j x ∧ η j x ≤ 1) ∧
        ∃ L : ℝ≥0, LipschitzWith L (η j)) ∧
      ∀ x ∈ ball c R, ∀ᶠ j in atTop, η j x = 1 := by
  by_cases hR : 0 < R
  · obtain ⟨r, hrMono, hr, hrLim⟩ := exists_seq_strictMono_tendsto' hR
    let b (j : ℕ) : ContDiffBump c :=
      ⟨r j, r (j + 1), (hr j).1, hrMono (Nat.lt_succ_self j)⟩
    refine ⟨fun j ↦ (b j : E → ℝ), ?_, ?_⟩
    · intro j
      refine ⟨(b j).contDiff, (b j).hasCompactSupport, ?_, ?_, ?_⟩
      · rw [(b j).tsupport_eq]
        exact closedBall_subset_ball (hr (j + 1)).2
      · intro x
        exact ⟨(b j).nonneg, (b j).le_one⟩
      · exact ContDiff.lipschitzWith_of_hasCompactSupport (b j).hasCompactSupport
          ((b j).contDiff : ContDiff ℝ ∞ (b j : E → ℝ)) (by simp)
    · intro x hx
      filter_upwards [hrLim.eventually (eventually_gt_nhds (mem_ball.mp hx))] with j hj
      exact (b j).one_of_mem_closedBall (mem_closedBall.mpr hj.le)
  · refine ⟨fun _ _ ↦ 0, ?_, ?_⟩
    · intro j
      refine ⟨contDiff_const, HasCompactSupport.zero, ?_, ?_, 0, LipschitzWith.const 0⟩
      · simp
      · intro x
        exact ⟨le_rfl, zero_le_one⟩
    · intro x hx
      exact ((not_lt_of_ge (le_of_not_gt hR))
        (dist_nonneg.trans_lt (mem_ball.mp hx))).elim

end DifferentialGeometry.Analysis

end
