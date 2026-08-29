import DifferentialGeometry.Analysis.Estimates.ProductBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace DifferentialGeometry.Analysis

private theorem four_mul_quadratic_le_eight_mul_one_add_sq (x : ℝ) :
    4 * (1 + 2 * x + x * x) ≤ 8 * (1 + x ^ 2) := by
  nlinarith [sq_nonneg (1 - x)]

theorem quartic_product_sum_le_interpolation_square
    {b c R A A4 D2 D3 D4 N x : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hR : 0 ≤ R) (hA : 0 ≤ A) (hA4 : 0 ≤ A4)
    (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) (hD4 : 0 ≤ D4) (hN : 0 ≤ N)
    (hxsq : x ^ 2 = c * (R * A4)) :
    b * (((1 + x) ^ 2 * (1 + x) ^ 2) * (D3 ^ 2 + N ^ 2)) ≤
      (Real.sqrt (8 * b) * (1 + A) * (D4 + D3 + D2 + N) +
        Real.sqrt (8 * b) * c * R * A4 * (D3 + N)) ^ 2 := by
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hb8 : (0 : ℝ) ≤ 8 * b := by linarith
  have hsq : Real.sqrt (8 * b) ^ 2 = 8 * b := Real.sq_sqrt hb8
  have hsn : 0 ≤ Real.sqrt (8 * b) := Real.sqrt_nonneg _
  have hu1 : u ≤ (D3 + N) ^ 2 := by
    rw [hu]
    exact sq_add_sq_le_sq_add_of_nonneg hD3 hN
  have hgeu : u ≤ (1 + A) ^ 2 * (D4 + D3 + D2 + N) ^ 2 := by
    have h2 : (D3 + N) ^ 2 ≤ (D4 + D3 + D2 + N) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hone : (1 : ℝ) ≤ (1 + A) ^ 2 := by
      simpa using
        (pow_le_pow_left₀ (a := (1 : ℝ)) (b := 1 + A) (by norm_num) (by linarith) 2)
    have h3 : (D4 + D3 + D2 + N) ^ 2 ≤
        (1 + A) ^ 2 * (D4 + D3 + D2 + N) ^ 2 := by
      calc
        (D4 + D3 + D2 + N) ^ 2 = 1 * (D4 + D3 + D2 + N) ^ 2 :=
          (one_mul _).symm
        _ ≤ (1 + A) ^ 2 * (D4 + D3 + D2 + N) ^ 2 :=
          mul_le_mul_of_nonneg_right hone (sq_nonneg _)
    linarith
  have hpl0 : (0 : ℝ) ≤ (1 + x) ^ 2 := sq_nonneg _
  have hpl4 : (1 + x) ^ 2 * (1 + x) ^ 2 ≤ 8 * (1 + (c * R * A4) ^ 2) := by
    have hX : x ^ 2 = c * R * A4 := by
      rw [hxsq]
      ring
    have hp : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by
      nlinarith [sq_nonneg (1 - x)]
    have hq : (1 + x) ^ 2 * (1 + x) ^ 2 ≤
        (2 * (1 + x ^ 2)) * (2 * (1 + x ^ 2)) :=
      mul_le_mul hp hp hpl0 (by positivity)
    refine hq.trans ?_
    have he : (2 * (1 + x ^ 2)) * (2 * (1 + x ^ 2)) =
        4 * (1 + 2 * x ^ 2 + x ^ 2 * x ^ 2) := by ring
    rw [he, hX]
    exact four_mul_quadratic_le_eight_mul_one_add_sq (c * R * A4)
  have hXnn : 0 ≤ Real.sqrt (8 * b) * (1 + A) * (D4 + D3 + D2 + N) :=
    mul_nonneg (mul_nonneg hsn (by linarith)) (by linarith)
  have hYnn : 0 ≤ Real.sqrt (8 * b) * c * R * A4 * (D3 + N) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hsn hc) hR) hA4)
      (by linarith)
  have hX2 : 8 * b * u ≤
      (Real.sqrt (8 * b) * (1 + A) * (D4 + D3 + D2 + N)) ^ 2 := by
    have he : (Real.sqrt (8 * b) * (1 + A) * (D4 + D3 + D2 + N)) ^ 2 =
        Real.sqrt (8 * b) ^ 2 *
          ((1 + A) ^ 2 * (D4 + D3 + D2 + N) ^ 2) := by ring
    rw [he, hsq]
    exact mul_le_mul_of_nonneg_left hgeu hb8
  have hY2 : 8 * b * (c * R * A4) ^ 2 * u ≤
      (Real.sqrt (8 * b) * c * R * A4 * (D3 + N)) ^ 2 := by
    have he : (Real.sqrt (8 * b) * c * R * A4 * (D3 + N)) ^ 2 =
        Real.sqrt (8 * b) ^ 2 *
          ((c * R * A4) ^ 2 * (D3 + N) ^ 2) := by ring
    have hcu : (c * R * A4) ^ 2 * u ≤ (c * R * A4) ^ 2 * (D3 + N) ^ 2 :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg _)
    rw [he, hsq]
    have hstep := mul_le_mul_of_nonneg_left hcu hb8
    refine le_trans (le_of_eq ?_) hstep
    ring
  have hstep1 : ((1 + x) ^ 2 * (1 + x) ^ 2) * u ≤
      (8 * (1 + (c * R * A4) ^ 2)) * u :=
    mul_le_mul_of_nonneg_right hpl4 hu0
  have hstep2 : b * (((1 + x) ^ 2 * (1 + x) ^ 2) * u) ≤
      b * ((8 * (1 + (c * R * A4) ^ 2)) * u) :=
    mul_le_mul_of_nonneg_left hstep1 hb
  have hstep3 : b * ((8 * (1 + (c * R * A4) ^ 2)) * u) =
      8 * b * u + 8 * b * (c * R * A4) ^ 2 * u := by ring
  have hsum := sq_add_sq_le_sq_add_of_nonneg hXnn hYnn
  calc
    b * (((1 + x) ^ 2 * (1 + x) ^ 2) * u) ≤
        b * ((8 * (1 + (c * R * A4) ^ 2)) * u) := hstep2
    _ = 8 * b * u + 8 * b * (c * R * A4) ^ 2 * u := hstep3
    _ ≤ (Real.sqrt (8 * b) * (1 + A) * (D4 + D3 + D2 + N)) ^ 2 +
        (Real.sqrt (8 * b) * c * R * A4 * (D3 + N)) ^ 2 :=
      add_le_add hX2 hY2
    _ ≤ (Real.sqrt (8 * b) * (1 + A) * (D4 + D3 + D2 + N) +
        Real.sqrt (8 * b) * c * R * A4 * (D3 + N)) ^ 2 := hsum

end DifferentialGeometry.Analysis
