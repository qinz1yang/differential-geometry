import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Set Real

namespace Real

private theorem middle_ray_square (a b : ℝ) :
    sin b ^ 2 + (sin (a + b) / 2) ^ 2 -
      2 * sin b * (sin (a + b) / 2) * cos a =
    (sin b ^ 2 + sin a ^ 2 - 2 * sin b * sin a * cos (a + b)) / 4 := by
  rw [sin_add, cos_add]
  linear_combination -(3 / 4 : ℝ) * sin b ^ 2 * sin_sq_add_cos_sq a +
    (1 / 4 : ℝ) * sin a ^ 2 * sin_sq_add_cos_sq b

theorem angle_triangle_of_cosine_distance_triangle {a b c : ℝ}
    (ha : a ∈ Icc (0 : ℝ) Real.pi) (hb : b ∈ Icc (0 : ℝ) Real.pi)
    (hc : c ∈ Icc (0 : ℝ) Real.pi)
    (htri : ∀ u v w : ℝ, 0 < u → 0 < v → 0 < w →
      sqrt (u ^ 2 + w ^ 2 - 2 * u * w * cos c) ≤
        sqrt (u ^ 2 + v ^ 2 - 2 * u * v * cos a) +
          sqrt (v ^ 2 + w ^ 2 - 2 * v * w * cos b)) :
    c ≤ a + b := by
  by_contra h
  have habc : a + b < c := lt_of_not_ge h
  let e := (c - a - b) / 4
  have he : 0 < e := by dsimp [e]; linarith
  let a' := a + e
  let b' := b + e
  have ha' : 0 < a' := by dsimp [a']; linarith [ha.1]
  have hb' : 0 < b' := by dsimp [b']; linarith [hb.1]
  have hab' : a' + b' < c := by dsimp [a', b', e]; linarith
  have habpi : a' + b' < Real.pi := hab'.trans_le hc.2
  have hapi : a' < Real.pi := by linarith
  have hbpi : b' < Real.pi := by linarith
  have hsa : 0 < sin a' := sin_pos_of_pos_of_lt_pi ha' hapi
  have hsb : 0 < sin b' := sin_pos_of_pos_of_lt_pi hb' hbpi
  have hsab : 0 < sin (a' + b') := sin_pos_of_pos_of_lt_pi (by linarith) habpi
  have hca : cos a' ≤ cos a := cos_le_cos_of_nonneg_of_le_pi ha.1 hapi.le (by dsimp [a']; linarith)
  have hcb : cos b' ≤ cos b := cos_le_cos_of_nonneg_of_le_pi hb.1 hbpi.le (by dsimp [b']; linarith)
  have hcc : cos c < cos (a' + b') := cos_lt_cos_of_nonneg_of_le_pi (by linarith) hc.2 hab'
  let D := sin b' ^ 2 + sin a' ^ 2 - 2 * sin b' * sin a' * cos (a' + b')
  have hD : 0 ≤ D := by
    dsimp only [D]
    nlinarith [cos_le_one (a' + b'), sq_nonneg (sin b' - sin a'),
      mul_nonneg (mul_pos hsb hsa).le (sub_nonneg.mpr (cos_le_one (a' + b')))]
  have h1 : sqrt (sin b' ^ 2 + (sin (a' + b') / 2) ^ 2 -
      2 * sin b' * (sin (a' + b') / 2) * cos a) ≤ sqrt (D / 4) := by
    apply sqrt_le_sqrt
    rw [show D / 4 = sin b' ^ 2 + (sin (a' + b') / 2) ^ 2 -
      2 * sin b' * (sin (a' + b') / 2) * cos a' from (middle_ray_square a' b').symm]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hca (by positivity)) _
  have h2 : sqrt ((sin (a' + b') / 2) ^ 2 + sin a' ^ 2 -
      2 * (sin (a' + b') / 2) * sin a' * cos b) ≤ sqrt (D / 4) := by
    apply sqrt_le_sqrt
    have hid := middle_ray_square b' a'
    rw [add_comm b' a'] at hid
    have heq : D / 4 = (sin (a' + b') / 2) ^ 2 + sin a' ^ 2 -
        2 * (sin (a' + b') / 2) * sin a' * cos b' := by
      dsimp only [D]
      nlinarith [hid]
    rw [heq]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hcb (by positivity)) _
  have hbound := (htri (sin b') (sin (a' + b') / 2) (sin a') hsb
    (div_pos hsab (by norm_num)) hsa).trans (add_le_add h1 h2)
  have hrad : D < sin b' ^ 2 + sin a' ^ 2 - 2 * sin b' * sin a' * cos c := by
    dsimp only [D]
    nlinarith [mul_pos (mul_pos hsb hsa) (sub_pos.mpr hcc)]
  have hsquare := sq_sqrt (show 0 ≤ D / 4 by positivity)
  have hsquare' := sq_sqrt (hD.trans hrad.le)
  have hroot := sqrt_nonneg (sin b' ^ 2 + sin a' ^ 2 - 2 * sin b' * sin a' * cos c)
  have hrootD := sqrt_nonneg (D / 4)
  nlinarith

end Real
