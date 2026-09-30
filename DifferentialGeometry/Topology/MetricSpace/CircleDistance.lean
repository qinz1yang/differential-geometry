import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace AddCircle

variable {L a b : ℝ}

theorem norm_coe_eq_min_of_mem_Icc (hL : 0 < L) (ha : a ∈ Icc (0 : ℝ) L) :
    ‖(a : AddCircle L)‖ = min a (L - a) := by
  by_cases haL : a ≤ L / 2
  · have hnorm : ‖(a : AddCircle L)‖ = |a| :=
      (norm_coe_eq_abs_iff L hL.ne').mpr (by rw [abs_of_nonneg ha.1, abs_of_pos hL]; exact haL)
    rw [hnorm, abs_of_nonneg ha.1, min_eq_left (by linarith)]
  · have hnorm : ‖((a - L : ℝ) : AddCircle L)‖ = |a - L| :=
      (norm_coe_eq_abs_iff L hL.ne').mpr (by
        rw [abs_of_nonpos (sub_nonpos.mpr ha.2), abs_of_pos hL]
        linarith)
    rw [coe_sub, coe_period, sub_zero] at hnorm
    rw [hnorm, abs_of_nonpos (sub_nonpos.mpr ha.2), min_eq_right (by linarith)]
    ring

theorem dist_coe_eq_abs_of_le_half_period (hL : 0 < L) (hab : |a - b| ≤ L / 2) :
    dist (a : AddCircle L) (b : AddCircle L) = |a - b| := by
  rw [dist_eq_norm, ← coe_sub]
  exact (norm_coe_eq_abs_iff L hL.ne').mpr (by rwa [abs_of_pos hL])

end AddCircle
