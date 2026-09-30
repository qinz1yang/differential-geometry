import DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

noncomputable def descendingIntervalProfile (a b x : ℝ) : ℝ :=
  CutoffProfile.value (1 + (x - a) / (b - a))

noncomputable def intervalPlateauProfile (a b c d x : ℝ) : ℝ :=
  descendingIntervalProfile (-b) (-a) (-x) * descendingIntervalProfile c d x

theorem contDiff_descendingIntervalProfile (a b : ℝ) :
    ContDiff ℝ ∞ (descendingIntervalProfile a b) :=
  CutoffProfile.contDiff.comp (contDiff_const.add ((contDiff_id.sub contDiff_const).div_const (b - a)))

theorem descendingIntervalProfile_mem_Icc (a b x : ℝ) :
    descendingIntervalProfile a b x ∈ Icc 0 1 := CutoffProfile.mem_Icc _

theorem descendingIntervalProfile_one {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    descendingIntervalProfile a b x = 1 := by
  apply CutoffProfile.one_of_le_one
  have hq : (x - a) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le
  linarith

theorem descendingIntervalProfile_zero {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    descendingIntervalProfile a b x = 0 := by
  apply CutoffProfile.zero_of_two_le
  have hq : 1 ≤ (x - a) / (b - a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  linarith

theorem antitone_descendingIntervalProfile {a b : ℝ} (hab : a < b) :
    Antitone (descendingIntervalProfile a b) := by
  intro x y hxy
  apply CutoffProfile.antitone_value
  linarith [div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le]

theorem contDiff_intervalPlateauProfile (a b c d : ℝ) :
    ContDiff ℝ ∞ (intervalPlateauProfile a b c d) :=
  ((contDiff_descendingIntervalProfile (-b) (-a)).comp contDiff_id.neg).mul
    (contDiff_descendingIntervalProfile c d)

theorem intervalPlateauProfile_mem_Icc (a b c d x : ℝ) :
    intervalPlateauProfile a b c d x ∈ Icc 0 1 := by
  have hl := descendingIntervalProfile_mem_Icc (-b) (-a) (-x)
  have hr := descendingIntervalProfile_mem_Icc c d x
  exact ⟨mul_nonneg hl.1 hr.1, (mul_le_mul_of_nonneg_left hr.2 hl.1).trans (by simpa using hl.2)⟩

theorem intervalPlateauProfile_zero_left {a b c d x : ℝ} (hab : a < b) (hx : x ≤ a) :
    intervalPlateauProfile a b c d x = 0 := by
  rw [intervalPlateauProfile, descendingIntervalProfile_zero (neg_lt_neg hab) (neg_le_neg hx), zero_mul]

theorem intervalPlateauProfile_zero_right {a b c d x : ℝ} (hcd : c < d) (hx : d ≤ x) :
    intervalPlateauProfile a b c d x = 0 := by
  rw [intervalPlateauProfile, descendingIntervalProfile_zero hcd hx, mul_zero]

theorem intervalPlateauProfile_one {a b c d x : ℝ} (hab : a < b) (hcd : c < d)
    (hx : x ∈ Icc b c) : intervalPlateauProfile a b c d x = 1 := by
  rw [intervalPlateauProfile, descendingIntervalProfile_one (neg_lt_neg hab) (neg_le_neg hx.1),
    descendingIntervalProfile_one hcd hx.2, one_mul]

theorem tsupport_intervalPlateauProfile_subset {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    tsupport (intervalPlateauProfile a b c d) ⊆ Icc a d := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hout
  rcases not_and_or.mp hout with hlo | hhi
  · exact hx (intervalPlateauProfile_zero_left hab (le_of_not_ge hlo))
  · exact hx (intervalPlateauProfile_zero_right hcd (le_of_not_ge hhi))

end DifferentialGeometry.Analysis
