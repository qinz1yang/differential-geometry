import DifferentialGeometry.Geometry.Comparison.ModelAngleStability
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

open Set Filter Real Metric Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem cradle_step_bounds {ℓ a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hlower : 2 * ℓ / 3 ≤ a + b) (hupper : a + b < ℓ) :
    let h := (2 * ℓ / 3 - a) / 3
    ℓ / 18 < h ∧ h ≤ 2 * ℓ / 9 ∧ h < b ∧ a + h < 5 * ℓ / 9 ∧
      a + 2 * h < 11 * ℓ / 18 ∧ ℓ / 9 ≤ b - h := by
  dsimp only
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem cradle_recurrence_deficit_and_arms
    {ℓ : ℝ} (hℓ : 0 < ℓ) {a b c : ℕ → ℝ}
    (hwindow : ∀ n, 0 ≤ a n ∧ a n ≤ b n ∧ 2 * ℓ / 3 ≤ a n + b n ∧ a n + b n < ℓ)
    (hc : ∀ n, 0 ≤ c n ∧ c n ≤ a n + (2 * ℓ / 3 - a n) / 3)
    (harec : ∀ n, a (n + 1) = min (c n) (b n - (2 * ℓ / 3 - a n) / 3))
    (hbrec : ∀ n, b (n + 1) = max (c n) (b n - (2 * ℓ / 3 - a n) / 3)) :
    Tendsto (fun n => a n + b n - (a (n + 1) + b (n + 1))) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, a n ∈ Icc (ℓ / 36) ℓ ∧ b n ∈ Icc (ℓ / 36) ℓ := by
  let r : ℕ → ℝ := fun n => a n + b n
  let h : ℕ → ℝ := fun n => (2 * ℓ / 3 - a n) / 3
  have hsum (n : ℕ) : r (n + 1) = c n + b n - h n := by
    dsimp only [r]
    rw [harec, hbrec, min_add_max]
    ring
  have hanti : Antitone r := by
    apply antitone_nat_of_succ_le
    intro n
    rw [hsum]
    have hn := (hc n).2
    dsimp only [r, h]
    linarith
  have hr := tendsto_atTop_ciInf hanti
    (show BddBelow (range r) from ⟨2 * ℓ / 3, by
      rintro v ⟨n, rfl⟩
      exact (hwindow n).2.2.1⟩)
  have hδ : Tendsto (fun n => r n - r (n + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self] using hr.sub (hr.comp (tendsto_add_atTop_nat 1))
  refine ⟨hδ, ?_⟩
  have hsmall := Metric.tendsto_nhds.mp hδ (ℓ / 36) (by positivity)
  have hnext : ∀ᶠ n in atTop, a (n + 1) ∈ Icc (ℓ / 36) ℓ ∧
      b (n + 1) ∈ Icc (ℓ / 36) ℓ := by
    filter_upwards [hsmall] with n hn
    have hw := hwindow n
    have hw' := hwindow (n + 1)
    have hstep := cradle_step_bounds hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
    have hδlt : r n - r (n + 1) < ℓ / 36 :=
      (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hn)
    rw [hsum] at hδlt
    have hclower : ℓ / 36 ≤ c n := by
      dsimp only [r, h] at hδlt
      linarith [hstep.1]
    have halower : ℓ / 36 ≤ a (n + 1) := by
      rw [harec]
      apply le_min hclower
      linarith [hstep.2.2.2.2.2]
    exact ⟨⟨halower, by linarith [hw'.1, hw'.2.1, hw'.2.2.2]⟩,
      ⟨halower.trans hw'.2.1, by linarith [hw'.1, hw'.2.2.2]⟩⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnext
  apply eventually_atTop.mpr
  refine ⟨N + 1, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  exact hN m (by omega)

theorem tendsto_comparisonAngleNegCurvature_pi_of_cradle_recurrence
    {κ ℓ : ℝ} (hκ : 0 ≤ κ) (hℓ : 0 < ℓ) {a b c : ℕ → ℝ}
    (hwindow : ∀ n, 0 ≤ a n ∧ a n ≤ b n ∧ 2 * ℓ / 3 ≤ a n + b n ∧ a n + b n < ℓ)
    (hc : ∀ n, 0 ≤ c n ∧ c n ≤ a n + (2 * ℓ / 3 - a n) / 3)
    (harec : ∀ n, a (n + 1) = min (c n) (b n - (2 * ℓ / 3 - a n) / 3))
    (hbrec : ∀ n, b (n + 1) = max (c n) (b n - (2 * ℓ / 3 - a n) / 3)) :
    Tendsto (fun n => comparisonAngleNegCurvature κ (a n)
      ((2 * ℓ / 3 - a n) / 3) (c n)) atTop (𝓝 Real.pi) := by
  obtain ⟨hδ, harms⟩ := cradle_recurrence_deficit_and_arms hℓ hwindow hc harec hbrec
  apply tendsto_comparisonAngleNegCurvature_pi_of_deficit hκ (by positivity : 0 < ℓ / 36)
    (Lmax := ℓ)
  · filter_upwards [harms] with n hn
    have hw := hwindow n
    have hs := cradle_step_bounds hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
    exact ⟨hn.1, ⟨by linarith [hs.1], by linarith [hs.2.1]⟩, hc n⟩
  · convert hδ using 1
    funext n
    rw [harec, hbrec, min_add_max]
    ring

end DifferentialGeometry.Geometry.Comparison.Toponogov
