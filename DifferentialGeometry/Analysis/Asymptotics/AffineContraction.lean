import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

section

namespace DifferentialGeometry.Analysis

theorem le_pow_mul_add_defect_of_affine_contraction
    {e : ℕ → ℝ} {θ δ : ℝ} (hθ : 0 ≤ θ)
    (hstep : ∀ j, e (j + 1) ≤ θ * e j + (1 - θ) * δ) (k : ℕ) :
    e k ≤ θ ^ k * e 0 + (1 - θ ^ k) * δ := by
  have h := le_geom (u := fun j => e j - δ) hθ k (fun j _ => by
    nlinarith [hstep j])
  nlinarith

end DifferentialGeometry.Analysis

end
