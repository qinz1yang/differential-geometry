import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalized_scale_in_affine_coordinates {ρ : E → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (p : E) (hp : 0 < ρ p) {L : ℝ} (hsmall : L * Λ ≤ 1 / 2) :
    let σ : E → ℝ := fun x => ρ (p + ρ p • x) / ρ p
    LipschitzWith Λ σ ∧ σ 0 = 1 ∧ ∀ x ∈ Metric.closedBall (0 : E) L,
      |σ x - 1| ≤ L * Λ ∧ ‖fderiv ℝ σ x‖ ≤ Λ ∧ σ x ∈ Set.Icc (1 / 2) (3 / 2) := by
  let σ : E → ℝ := fun x => ρ (p + ρ p • x) / ρ p
  have hσ : LipschitzWith Λ σ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (ρ (p + ρ p • x) / ρ p) (ρ (p + ρ p • y) / ρ p) ≤ _
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    have hh := hρ.dist_le_mul (p + ρ p • x) (p + ρ p • y)
    rw [Real.dist_eq, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_eq_abs, abs_of_pos hp, ← dist_eq_norm] at hh
    exact hh.trans_eq (by ring)
  have hzero : σ 0 = 1 := by simp [σ, hp.ne']
  refine ⟨hσ, hzero, ?_⟩
  intro x hx
  have hclose : |σ x - 1| ≤ L * Λ := by
    have hh := hσ.dist_le_mul x 0
    rw [Real.dist_eq, hzero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hx (NNReal.coe_nonneg Λ)).trans_eq (mul_comm _ _))
  refine ⟨hclose, norm_fderiv_le_of_lipschitz ℝ hσ, ?_⟩
  exact ⟨by linarith [(abs_le.mp hclose).1], by linarith [(abs_le.mp hclose).2]⟩

end DifferentialGeometry.Analysis
