import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

open Filter
open scoped Topology InnerProductSpace

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_deriv_norm_sq {f : ℝ → E} {x : ℝ}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hf' : DifferentiableAt ℝ (deriv f) x) :
    HasDerivAt (deriv (fun y => ‖f y‖ ^ 2))
      (2 * ‖deriv f x‖ ^ 2 + 2 * ⟪f x, deriv (deriv f) x⟫_ℝ) x := by
  have heq : deriv (fun y => ‖f y‖ ^ 2) =ᶠ[𝓝 x]
      fun y => 2 * ⟪f y, deriv f y⟫_ℝ := by
    filter_upwards [hf] with y hy
    exact hy.hasDerivAt.norm_sq.deriv
  have hd₀ := (hf.self_of_nhds.hasDerivAt.inner ℝ hf'.hasDerivAt).const_mul 2
  have hd := hd₀.congr_of_eventuallyEq heq
  have hvalue : 2 * ‖deriv f x‖ ^ 2 + 2 * ⟪f x, deriv (deriv f) x⟫_ℝ =
      2 * (⟪f x, deriv (deriv f) x⟫_ℝ + ⟪deriv f x, deriv f x⟫_ℝ) := by
    rw [real_inner_self_eq_norm_sq]
    ring
  rw [hvalue]
  exact hd

theorem deriv_deriv_norm_sq {f : ℝ → E} {x : ℝ}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hf' : DifferentiableAt ℝ (deriv f) x) :
    deriv (deriv (fun y => ‖f y‖ ^ 2)) x =
      2 * ‖deriv f x‖ ^ 2 + 2 * ⟪f x, deriv (deriv f) x⟫_ℝ :=
  (hasDerivAt_deriv_norm_sq hf hf').deriv

end DifferentialGeometry.Analysis
