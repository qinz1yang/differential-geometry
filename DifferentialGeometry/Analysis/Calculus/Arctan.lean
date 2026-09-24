import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

theorem hasDerivAt_arctan_mul_div {a : ℝ → ℝ} {a' d b x : ℝ} (hb : 0 < b)
    (ha : HasDerivAt a a' x) :
    HasDerivAt (fun y : ℝ => Real.arctan (d * a y / b))
      (b * d * a' / (d ^ 2 * (a x) ^ 2 + b ^ 2)) x := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hcomp := (Real.hasDerivAt_arctan (d * a x / b)).comp x
    ((ha.const_mul d).div_const b)
  have hval : 1 / (1 + (d * a x / b) ^ 2) * (d * a' / b) =
      b * d * a' / (d ^ 2 * (a x) ^ 2 + b ^ 2) := by
    field_simp
    ring
  simpa only [Function.comp_def, hval] using hcomp

theorem deriv_arctan_mul_div {a : ℝ → ℝ} {a' d b x : ℝ} (hb : 0 < b)
    (ha : HasDerivAt a a' x) :
    deriv (fun y : ℝ => Real.arctan (d * a y / b)) x =
      b * d * a' / (d ^ 2 * (a x) ^ 2 + b ^ 2) :=
  (hasDerivAt_arctan_mul_div hb ha).deriv

private theorem sqrt_sq_unit_tangent_deriv_eq_abs_deriv_arctan
    {a : ℝ → ℝ} {a' d b x : ℝ} (hb : 0 < b)
    (ha : HasDerivAt a a' x) :
    Real.sqrt ((b * d * a') ^ 2 /
      (d ^ 2 * (a x) ^ 2 + b ^ 2) ^ 2) =
      |deriv (fun y : ℝ => Real.arctan (d * a y / b)) x| := by
  rw [deriv_arctan_mul_div hb ha, Real.sqrt_div (by positivity)]
  rw [Real.sqrt_sq_eq_abs, abs_div]
  rw [Real.sqrt_sq_eq_abs]


theorem hasDerivAt_mul_sq_add_sq_sqrt {a : ℝ → ℝ} {a' d b x : ℝ} (hb : 0 < b)
    (ha : HasDerivAt a a' x) :
    HasDerivAt (fun y : ℝ => Real.sqrt (d ^ 2 * (a y) ^ 2 + b ^ 2))
      (d ^ 2 * a x * a' / Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2)) x := by
  have hden : 0 < d ^ 2 * (a x) ^ 2 + b ^ 2 := by positivity
  have harg : HasDerivAt (fun y : ℝ => d ^ 2 * (a y) ^ 2 + b ^ 2)
      (2 * d ^ 2 * a x * a') x := by
    have h := ((ha.mul ha).const_mul (d ^ 2)).add_const (b ^ 2)
    have hval : d ^ 2 * (a' * a x + a x * a') = 2 * d ^ 2 * a x * a' := by ring
    rw [hval] at h
    simpa only [Pi.mul_apply, pow_two] using h
  convert harg.sqrt hden.ne' using 1
  ring

theorem hasDerivAt_div_mul_sq_add_sq_sqrt {a : ℝ → ℝ} {a' d b x : ℝ} (hb : 0 < b)
    (ha : HasDerivAt a a' x) :
    HasDerivAt (fun y : ℝ => a y / Real.sqrt (d ^ 2 * (a y) ^ 2 + b ^ 2))
      (b ^ 2 * a' / Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) ^ 3) x := by
  have hden : 0 < d ^ 2 * (a x) ^ 2 + b ^ 2 := by positivity
  have hspos : 0 < Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) := Real.sqrt_pos.mpr hden
  have hs := Real.sq_sqrt hden.le
  have hquot := ha.div (hasDerivAt_mul_sq_add_sq_sqrt hb ha) hspos.ne'
  have hval : (a' * Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) -
      a x * (d ^ 2 * a x * a' / Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2))) /
      (Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2)) ^ 2 =
      b ^ 2 * a' / Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) ^ 3 := by
    field_simp
    rw [hs]
    ring
  rwa [hval] at hquot

theorem hasDerivAt_inv_mul_sq_add_sq_sqrt {a : ℝ → ℝ} {a' d b x : ℝ} (hb : 0 < b)
    (ha : HasDerivAt a a' x) :
    HasDerivAt (fun y : ℝ => (Real.sqrt (d ^ 2 * (a y) ^ 2 + b ^ 2))⁻¹)
      (-d ^ 2 * a x * a' / Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) ^ 3) x := by
  have hden : 0 < d ^ 2 * (a x) ^ 2 + b ^ 2 := by positivity
  have hspos : 0 < Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) := Real.sqrt_pos.mpr hden
  have hinv := (hasDerivAt_mul_sq_add_sq_sqrt hb ha).inv hspos.ne'
  have hval : -(d ^ 2 * a x * a' / Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2)) /
      Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) ^ 2 =
      -d ^ 2 * a x * a' / Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) ^ 3 := by
    ring
  rw [hval] at hinv
  exact hinv

theorem sq_deriv_div_sqrt_add_sq_deriv_inv_sqrt
    {a : ℝ → ℝ} {a' d b x : ℝ} (hb : 0 < b) (ha : HasDerivAt a a' x) :
    d ^ 2 * (deriv (fun y : ℝ => a y / Real.sqrt (d ^ 2 * (a y) ^ 2 + b ^ 2)) x) ^ 2 +
      b ^ 2 * (deriv (fun y : ℝ => (Real.sqrt (d ^ 2 * (a y) ^ 2 + b ^ 2))⁻¹) x) ^ 2 =
      (b * d * a') ^ 2 / (d ^ 2 * (a x) ^ 2 + b ^ 2) ^ 2 := by
  rw [(hasDerivAt_div_mul_sq_add_sq_sqrt hb ha).deriv,
    (hasDerivAt_inv_mul_sq_add_sq_sqrt hb ha).deriv]
  have hden : 0 < d ^ 2 * (a x) ^ 2 + b ^ 2 := by positivity
  have hs := Real.sq_sqrt hden.le
  have hspos : 0 < Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) := Real.sqrt_pos.mpr hden
  field_simp
  rw [show Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) ^ 6 =
    (Real.sqrt (d ^ 2 * (a x) ^ 2 + b ^ 2) ^ 2) ^ 3 by ring, hs]
  ring

theorem sqrt_sq_deriv_div_sqrt_add_sq_deriv_inv_sqrt_eq_abs_deriv_arctan
    {a : ℝ → ℝ} {a' d b x : ℝ} (hb : 0 < b) (ha : HasDerivAt a a' x) :
    Real.sqrt
      (d ^ 2 * (deriv (fun y : ℝ => a y / Real.sqrt (d ^ 2 * (a y) ^ 2 + b ^ 2)) x) ^ 2 +
        b ^ 2 * (deriv (fun y : ℝ => (Real.sqrt (d ^ 2 * (a y) ^ 2 + b ^ 2))⁻¹) x) ^ 2) =
      |deriv (fun y : ℝ => Real.arctan (d * a y / b)) x| := by
  rw [sq_deriv_div_sqrt_add_sq_deriv_inv_sqrt hb ha,
    sqrt_sq_unit_tangent_deriv_eq_abs_deriv_arctan hb ha]
