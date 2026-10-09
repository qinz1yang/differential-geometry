import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The early derivative constant of the original block map (CGP02, arithmetic kernel)

Blueprint 207B, CGP02 (`prop:fibration-actual-global-derivative`, B:3956–4002). With FC02's
assembly bound `‖D𝓔⁰‖ ≤ (Λ² + N' B² + B_E²)^{1/2}` (`N' = N + 1` active constant-radius blocks),
the block budgets of CGP02's proof — `B ≤ 2 + 80 P₀`, the `E'` marker
`ρ|dζ_{E'}| ≤ (22 P₀ + (25/2) N P₀²)/Δ ≤ 40 (N+1) P₀²/Δ`, the variable-block constant
`B_E ≤ 500 (N+1) P₀²` (using `ρ|dt| ≤ 2`, `t ≤ 9Δ`, `ΔΛ ≤ 1/10`, `Δ ≥ 1`), and `Λ ≤ 1` — give
`(GD) ‖DF‖ ≤ L₀ = 1000 (N+2) P₀²`. These are the inequalities proved here; FC02 itself (the
square-sum over the actual blocks) and the actual block bounds are NOT in the tree.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Collapse

/-- CGP02: the `E'` marker bound and the variable-block constant. -/
theorem joint_block_budget {N P Δ Λ : ℝ} (hN : 0 ≤ N) (hP : 1 ≤ P) (hΔ : 1 ≤ Δ) (hΛ0 : 0 ≤ Λ)
    (hΔΛ : Δ * Λ ≤ 1 / 10) :
    (22 * P + 25 / 2 * N * P ^ 2) / Δ ≤ 40 * (N + 1) * P ^ 2 / Δ ∧
      2 + (9 * Δ + 1) * (40 * (N + 1) * P ^ 2 / Δ + Λ) ≤ 500 * (N + 1) * P ^ 2 := by
  have hΔ0 : 0 < Δ := by linarith
  have hP2 : P ≤ P ^ 2 := by nlinarith
  refine ⟨div_le_div_of_nonneg_right (by nlinarith) hΔ0.le, ?_⟩
  have hk : 0 ≤ 40 * (N + 1) * P ^ 2 := by positivity
  have h1 : (9 * Δ + 1) * (40 * (N + 1) * P ^ 2 / Δ) ≤ 10 * (40 * (N + 1) * P ^ 2) := by
    rw [mul_div_assoc', div_le_iff₀ hΔ0]
    nlinarith
  have h2 : (9 * Δ + 1) * Λ ≤ 1 := by nlinarith
  have hP1 : 1 ≤ (N + 1) * P ^ 2 := by nlinarith
  nlinarith

/-- CGP02 (GD): the square-sum of the block budgets is at most `1000 (N+2) P₀²`. -/
theorem early_derivative_constant {N P Λ B BE : ℝ} (hN : 0 ≤ N) (hP : 1 ≤ P) (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ 1) (hB0 : 0 ≤ B) (hB : B ≤ 2 + 80 * P) (hBE0 : 0 ≤ BE)
    (hBE : BE ≤ 500 * (N + 1) * P ^ 2) :
    Real.sqrt (Λ ^ 2 + (N + 1) * B ^ 2 + BE ^ 2) ≤ 1000 * (N + 2) * P ^ 2 := by
  rw [Real.sqrt_le_left (by positivity)]
  have hB' : B ≤ 82 * P := by linarith
  have hBsq : B ^ 2 ≤ 6724 * P ^ 2 := by nlinarith
  have hBEsq : BE ^ 2 ≤ 250000 * (N + 1) ^ 2 * (P ^ 2) ^ 2 := by
    have := pow_le_pow_left₀ hBE0 hBE 2
    nlinarith
  have hP2 : 1 ≤ P ^ 2 := by nlinarith
  have hQ : 1 ≤ (N + 2) * P ^ 2 := by nlinarith
  have hΛsq : Λ ^ 2 ≤ 1 := by nlinarith
  have h1 : (N + 1) * B ^ 2 ≤ 6724 * ((N + 2) * P ^ 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hBsq (by linarith : (0 : ℝ) ≤ N + 1)
    nlinarith
  have h2 : BE ^ 2 ≤ 250000 * ((N + 2) * P ^ 2) ^ 2 := by nlinarith
  have h3 : (1 : ℝ) ≤ ((N + 2) * P ^ 2) ^ 2 := by nlinarith
  nlinarith

end DifferentialGeometry.Geometry.Collapse
