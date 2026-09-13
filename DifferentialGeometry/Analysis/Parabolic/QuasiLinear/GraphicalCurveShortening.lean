import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def graphDiffusionCoefficient (p : E) : ℝ := (1 + ‖p‖ ^ 2)⁻¹

theorem graphDiffusionCoefficient_pos (p : E) : 0 < graphDiffusionCoefficient p := by
  unfold graphDiffusionCoefficient
  positivity

theorem graphDiffusionCoefficient_le_one (p : E) : graphDiffusionCoefficient p ≤ 1 := by
  unfold graphDiffusionCoefficient
  exact (inv_le_one₀ (by positivity)).2 (by nlinarith [sq_nonneg ‖p‖])

variable [InnerProductSpace ℝ E]

private theorem graph_reaction_square_bound (p q r : E) {a : ℝ} (ha : 0 ≤ a) :
    -2 * a * ‖r‖ ^ 2 - 8 * a ^ 2 * ⟪p, q⟫_ℝ * ⟪q, r⟫_ℝ -
      4 * a ^ 2 * ‖q‖ ^ 2 * ⟪p, r⟫_ℝ +
      16 * a ^ 3 * ⟪p, q⟫_ℝ ^ 2 * ‖q‖ ^ 2 - 4 * a ^ 2 * ‖q‖ ^ 4 ≤
        -a * ‖r‖ ^ 2 + a ^ 2 * (52 * a * ‖p‖ ^ 2 - 4) * ‖q‖ ^ 4 := by
  have hsquare := mul_nonneg ha (real_inner_self_nonneg (x :=
    r + (4 * a * ⟪p, q⟫_ℝ) • q + (2 * a * ‖q‖ ^ 2) • p))
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hsquare
  have hcs := real_inner_mul_inner_self_le p q
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hscaled := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 48 * a ^ 3 * ‖q‖ ^ 2)
  simp only [real_inner_comm] at hsquare hscaled ⊢
  linear_combination hscaled + hsquare

theorem graph_second_derivative_reaction_le (p q r : E) (hp : ‖p‖ ≤ 1 / 4) :
    let a := graphDiffusionCoefficient p;
    -2 * a * ‖r‖ ^ 2 - 8 * a ^ 2 * ⟪p, q⟫_ℝ * ⟪q, r⟫_ℝ -
      4 * a ^ 2 * ‖q‖ ^ 2 * ⟪p, r⟫_ℝ +
      16 * a ^ 3 * ⟪p, q⟫_ℝ ^ 2 * ‖q‖ ^ 2 - 4 * a ^ 2 * ‖q‖ ^ 4 ≤
        -(1 / 2 : ℝ) * ‖q‖ ^ 4 := by
  let a := graphDiffusionCoefficient p
  have ha : 0 < a := graphDiffusionCoefficient_pos p
  have ha1 : a ≤ 1 := graphDiffusionCoefficient_le_one p
  have hp2 : ‖p‖ ^ 2 ≤ 1 / 16 := by nlinarith [norm_nonneg p]
  have halower : (16 / 17 : ℝ) ≤ a := by
    dsimp [a, graphDiffusionCoefficient]
    rw [← one_div]
    apply (le_div_iff₀ (by positivity : 0 < 1 + ‖p‖ ^ 2)).2
    nlinarith only [hp2]
  have hneg : 52 * a * ‖p‖ ^ 2 - 4 ≤ -(3 / 4 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right ha1 (sq_nonneg ‖p‖)
    nlinarith only [hmul, hp2]
  have hcoef : a ^ 2 * (52 * a * ‖p‖ ^ 2 - 4) ≤ -(1 / 2 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hneg (sq_nonneg a)
    have hasq : (16 / 17 : ℝ) ^ 2 ≤ a ^ 2 := by nlinarith only [halower, sq_nonneg (a - 16 / 17)]
    nlinarith only [hmul, hasq]
  have hbound := graph_reaction_square_bound p q r ha.le
  have hscaled := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ ‖q‖ ^ 4)
  have hgrad : 0 ≤ a * ‖r‖ ^ 2 := by positivity
  exact hbound.trans (by nlinarith only [hscaled, hgrad])

end DifferentialGeometry.Analysis.Parabolic
