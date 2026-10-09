import DifferentialGeometry.Analysis.Order.CommonProfile
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Filter
open scoped Topology

namespace GC.GeneralFlow

theorem commonProfile_tendsto_zero {b : ℕ → ℝ}
    (hb : ∀ n, 0 < b n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n, b n < ε) :
    Tendsto (commonProfile b) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun t => ha.trans (commonProfile_pos hb t)
  · intro ε hε
    obtain ⟨n, hn⟩ := hsmall ε hε
    filter_upwards [eventually_ge_atTop (n : ℝ)] with t ht
    exact ((commonProfile_interval_budgets hb n t ht).1).trans hn

theorem exists_decaying_commonProfile {b : ℕ → ℝ} (hb : ∀ n, 0 < b n) :
    ∃ δ : ℝ → ℝ, (∀ t, 0 < δ t) ∧ Antitone δ ∧ (∀ t, δ t < 1) ∧
      Tendsto δ atTop (𝓝 0) ∧
      ∀ (n : ℕ) (t : ℝ), (n : ℝ) ≤ t → δ t < b n ∧ δ t < b (n + 1) := by
  let a : ℕ → ℝ := fun n => min (b n) (((n : ℝ) + 1)⁻¹)
  have ha : ∀ n, 0 < a n := fun n => lt_min (hb n) (by positivity)
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ n, a n < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, (min_le_right _ _).trans_lt (by simpa only [one_div] using hn)⟩
  refine ⟨commonProfile a, commonProfile_pos ha, commonProfile_antitone a,
    commonProfile_lt_one a, commonProfile_tendsto_zero ha hsmall, ?_⟩
  intro n t ht
  obtain ⟨h₀, h₁⟩ := commonProfile_interval_budgets ha n t ht
  exact ⟨h₀.trans_le (min_le_left _ _), h₁.trans_le (min_le_left _ _)⟩

end GC.GeneralFlow
