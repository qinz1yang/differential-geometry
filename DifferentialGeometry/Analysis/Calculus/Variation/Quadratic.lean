import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem tendsto_zero_of_quadratic_variations
    {ι : Type*} {l : Filter ι} {E S : ι → ℝ} {Q : ι → ℝ → ℝ}
    {m ε C : ℝ} (hε : 0 < ε) (hE : Tendsto E l (𝓝 m))
    (hlower : ∀ t : ℝ, |t| < ε → ∀ᶠ n in l, m ≤ Q n t)
    (hquadratic : ∀ t : ℝ, |t| < ε →
      ∀ᶠ n in l, |Q n t - E n - t * S n| ≤ C * t ^ 2 * E n) :
    Tendsto S l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let B : ℝ := |C| * (|m| + 1)
  have hB : 0 ≤ B := by positivity
  have hdenom : 0 < 4 * (B + 1) := by positivity
  let δ : ℝ := min (ε / 2) (η / (4 * (B + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hη hdenom)
  have hδ_le : δ ≤ ε / 2 := min_le_left _ _
  have hδ_lt : δ < ε := by linarith
  have hδ_scale : δ * (4 * (B + 1)) ≤ η :=
    (le_div_iff₀ hdenom).mp (min_le_right _ _)
  have hδB : δ * B < η / 2 := by nlinarith
  have hsmall : δ ^ 2 * B < δ * η / 2 := by
    nlinarith [mul_lt_mul_of_pos_left hδB hδ]
  have hδ_abs : |δ| < ε := by rwa [abs_of_pos hδ]
  have hnegδ_abs : |-δ| < ε := by rwa [abs_neg]
  filter_upwards [Metric.tendsto_nhds.mp hE 1 (by norm_num),
    Metric.tendsto_nhds.mp hE (δ * η / 2) (by positivity),
    hlower δ hδ_abs, hlower (-δ) hnegδ_abs,
    hquadratic δ hδ_abs, hquadratic (-δ) hnegδ_abs]
    with n hn_one hn_close hn_lower_pos hn_lower_neg hn_pos hn_neg
  rw [Real.dist_eq] at hn_one hn_close
  have hn_abs : |E n| ≤ |m| + 1 := by
    have hn := abs_lt.mp hn_one
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le m]
    · linarith [le_abs_self m]
  have hgap : E n - m < δ * η / 2 := (abs_lt.mp hn_close).2
  have hrem : C * δ ^ 2 * E n ≤ δ ^ 2 * B := by
    calc
      C * δ ^ 2 * E n ≤ |C * δ ^ 2 * E n| := le_abs_self _
      _ = |C| * δ ^ 2 * |E n| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg δ)]
      _ ≤ |C| * δ ^ 2 * (|m| + 1) :=
        mul_le_mul_of_nonneg_left hn_abs (by positivity)
      _ = δ ^ 2 * B := by dsimp [B]; ring
  have hpos := (abs_le.mp hn_pos).2
  have hneg := (abs_le.mp hn_neg).2
  rw [Real.dist_eq, sub_zero]
  apply abs_lt.mpr
  constructor
  · apply (mul_lt_mul_iff_right₀ hδ).mp
    nlinarith only [hn_lower_pos, hpos, hrem, hgap, hsmall]
  · apply (mul_lt_mul_iff_right₀ hδ).mp
    nlinarith only [hn_lower_neg, hneg, hrem, hgap, hsmall]

end DifferentialGeometry.Analysis
