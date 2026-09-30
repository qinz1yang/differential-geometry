import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace GC.GeneralFlow
noncomputable def roundReserveBallConstant (κ A B : ℝ) : ℝ :=
  κ * Real.exp (-(18*A*Real.sqrt B)) / (6912*A^3)

theorem roundReserveBallConstant_lt {κ A B : ℝ}
    (hκ : 0 < κ) (hA : 1 ≤ A) :
    roundReserveBallConstant κ A B < κ := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hpow : 1 ≤ A^3 := one_le_pow₀ hA
  have hd : 1 < 6912*A^3 := by nlinarith
  have he : Real.exp (-(18*A*Real.sqrt B)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  unfold roundReserveBallConstant
  apply (div_lt_iff₀ (zero_lt_one.trans hd)).mpr
  calc
    κ * Real.exp (-(18*A*Real.sqrt B)) ≤ κ*1 := mul_le_mul_of_nonneg_left he hκ.le
    _ < κ*(6912*A^3) := mul_lt_mul_of_pos_left hd hκ

theorem same_kappa_bootstrap_impossible {κ A B : ℝ}
    (hκ : 0 < κ) (hA : 1 ≤ A) :
    ¬ κ ≤ roundReserveBallConstant κ A B :=
  not_le_of_gt (roundReserveBallConstant_lt hκ hA)

end GC.GeneralFlow
