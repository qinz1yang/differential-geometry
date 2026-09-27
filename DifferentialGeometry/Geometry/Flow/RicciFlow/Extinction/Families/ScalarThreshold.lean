import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

def extinctionThreshold (c A : ℝ) : ℝ :=
  (c ^ (1 / 4 : ℝ) + A / (8 * Real.pi * c ^ (3 / 4 : ℝ))) ^ 4 - c

private theorem fourth_root_pow {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
  simpa using Real.rpow_inv_natCast_pow hx (by norm_num : (4 : ℕ) ≠ 0)

theorem extinctionThreshold_nonneg {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) :
    0 ≤ extinctionThreshold c A := by
  have hp : 0 < 8 * Real.pi * c ^ (3 / 4 : ℝ) := by positivity
  have hroot : 0 ≤ c ^ (1 / 4 : ℝ) := Real.rpow_nonneg hc.le _
  have h := pow_le_pow_left₀ hroot
    (le_add_of_nonneg_right (div_nonneg hA hp.le)) 4
  rw [fourth_root_pow hc.le] at h
  exact sub_nonneg.mpr h

theorem extinctionThreshold_strictMonoOn {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (extinctionThreshold c) (Ici 0) := by
  intro A hA B _ hAB
  have hp : 0 < 8 * Real.pi * c ^ (3 / 4 : ℝ) := by positivity
  have hz : 0 ≤ c ^ (1 / 4 : ℝ) + A / (8 * Real.pi * c ^ (3 / 4 : ℝ)) :=
    add_nonneg (Real.rpow_nonneg hc.le _) (div_nonneg hA hp.le)
  exact sub_lt_sub_right
    (pow_lt_pow_left₀ (show c ^ (1 / 4 : ℝ) + A / (8 * Real.pi * c ^ (3 / 4 : ℝ)) <
      c ^ (1 / 4 : ℝ) + B / (8 * Real.pi * c ^ (3 / 4 : ℝ)) from
        add_lt_add_right (div_lt_div_of_pos_right hAB hp) _)
      hz (by norm_num : (4 : ℕ) ≠ 0)) c

theorem extinctionThreshold_eq_zero_iff {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) :
    extinctionThreshold c A = 0 ↔ A = 0 := by
  have hzero : extinctionThreshold c 0 = 0 := by
    simp only [extinctionThreshold, zero_div, add_zero, fourth_root_pow hc.le, sub_self]
  constructor
  · intro heq
    by_contra hne
    have hlt := extinctionThreshold_strictMonoOn hc (show 0 ∈ Ici (0 : ℝ) from (le_refl (0 : ℝ)))
      hA (lt_of_le_of_ne hA (Ne.symm hne))
    rw [hzero, heq] at hlt
    exact (lt_irrefl 0) hlt
  · rintro rfl
    exact hzero

theorem extinctionThreshold_lt_iff {c A H : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hH : 0 ≤ H) :
    extinctionThreshold c A < H ↔
      A / c ^ (3 / 4 : ℝ) -
        8 * Real.pi * ((H + c) ^ (1 / 4 : ℝ) - c ^ (1 / 4 : ℝ)) < 0 := by
  have hc34 : 0 < c ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hc _
  have hp : 0 < 8 * Real.pi := by positivity
  have hsum : 0 < H + c := add_pos_of_nonneg_of_pos hH hc
  have hz : 0 ≤ c ^ (1 / 4 : ℝ) + A / (8 * Real.pi * c ^ (3 / 4 : ℝ)) :=
    add_nonneg (Real.rpow_nonneg hc.le _) (div_nonneg hA (mul_pos hp hc34).le)
  have hroot : 0 ≤ (H + c) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hsum.le _
  have hpowers := pow_lt_pow_iff_left₀ hz hroot (by norm_num : (4 : ℕ) ≠ 0)
  rw [fourth_root_pow hsum.le] at hpowers
  have hdivide : A / (8 * Real.pi * c ^ (3 / 4 : ℝ)) =
      (A / c ^ (3 / 4 : ℝ)) / (8 * Real.pi) := by ring
  rw [extinctionThreshold, sub_lt_iff_lt_add, hpowers, hdivide]
  constructor
  · intro h
    have hm := (div_lt_iff₀ hp).mp (show A / c ^ (3 / 4 : ℝ) / (8 * Real.pi) <
        (H + c) ^ (1 / 4 : ℝ) - c ^ (1 / 4 : ℝ) by linarith)
    nlinarith
  · intro h
    have hm : A / c ^ (3 / 4 : ℝ) / (8 * Real.pi) <
        (H + c) ^ (1 / 4 : ℝ) - c ^ (1 / 4 : ℝ) :=
      (div_lt_iff₀ hp).mpr (by nlinarith)
    linarith

theorem extinctionThreshold_mul {c a A : ℝ} (hc : 0 < c) (ha : 0 < a) :
    extinctionThreshold (a * c) (a * A) = a * extinctionThreshold c A := by
  have ha34 : a ^ (3 / 4 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  have hc34 : c ^ (3 / 4 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have hsplit : a ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) = a := by
    rw [← Real.rpow_add ha]
    norm_num
  have hquot : a * A / (8 * Real.pi * (a ^ (3 / 4 : ℝ) * c ^ (3 / 4 : ℝ))) =
      a ^ (1 / 4 : ℝ) * (A / (8 * Real.pi * c ^ (3 / 4 : ℝ))) := by
    calc
      _ = (a ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) * A /
          (8 * Real.pi * (a ^ (3 / 4 : ℝ) * c ^ (3 / 4 : ℝ))) := by rw [hsplit]
      _ = _ := by field_simp [ha34, hc34, Real.pi_ne_zero]
  simp only [extinctionThreshold, Real.mul_rpow ha.le hc.le]
  rw [hquot, ← mul_add, mul_pow, fourth_root_pow ha.le]
  ring

theorem extinctionThreshold_div {c A factor : ℝ} (hc : 0 < c) (hfactor : 0 < factor) :
    extinctionThreshold (c / factor) (A / factor) = extinctionThreshold c A / factor := by
  simpa only [div_eq_mul_inv, mul_comm] using
    (extinctionThreshold_mul (A := A) hc (inv_pos.mpr hfactor))

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
