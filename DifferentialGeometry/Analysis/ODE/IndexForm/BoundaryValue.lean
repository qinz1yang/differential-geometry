import DifferentialGeometry.Analysis.ODE.IndexForm.Positivity

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem IsJacobiFieldOn.eq_zero_of_endpoints_eq_zero
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {a b κ : ℝ}
    (hsol : IsJacobiFieldOn R a b y v)
    (hab : a ≤ b) (hya : y a = 0) (hyb : y b = 0)
    (hκ : κ * (b - a) ^ 2 < (Real.pi / 2) ^ 2)
    (hupper : ∀ t ∈ Ioo a b, ⟪R t (y t), y t⟫ ≤ κ * ‖y t‖ ^ 2) :
    EqOn y (fun _ => 0) (Icc a b) := by
  by_contra hne
  have hp := IsJacobiFieldOn.inner_velocity_position_at_right_pos
    hsol hab hya hne hκ hupper
  simp only [hyb, inner_zero_right, lt_self_iff_false] at hp

end DifferentialGeometry.Analysis.ODE
