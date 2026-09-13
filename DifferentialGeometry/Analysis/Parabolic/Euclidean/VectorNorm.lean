import DifferentialGeometry.Analysis.Calculus.Derivative.NormSq

open Filter
open scoped Topology InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sq_parabolic_eq {u : ℝ → ℝ → E} {x t a : ℝ}
    (hx : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => u y t) y)
    (hxx : DifferentiableAt ℝ (deriv (fun y => u y t)) x)
    (ht : DifferentiableAt ℝ (fun s => u x s) t) :
    deriv (fun s => ‖u x s‖ ^ 2) t - a * deriv (deriv (fun y => ‖u y t‖ ^ 2)) x =
      2 * ⟪u x t, deriv (fun s => u x s) t - a • deriv (deriv (fun y => u y t)) x⟫_ℝ -
        2 * a * ‖deriv (fun y => u y t) x‖ ^ 2 := by
  rw [ht.hasDerivAt.norm_sq.deriv, deriv_deriv_norm_sq hx hxx,
    inner_sub_right, real_inner_smul_right]
  ring

end DifferentialGeometry.Analysis.Parabolic
