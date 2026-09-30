import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
noncomputable section
open Set

namespace Metric

variable {Y : Type*} [PseudoMetricSpace Y]

def coneDistance (x y : ℝ × Y) : ℝ :=
  Real.sqrt (x.1 ^ 2 + y.1 ^ 2 - 2 * x.1 * y.1 * Real.cos (min Real.pi (dist x.2 y.2)))

theorem coneDistance_nonneg (x y : ℝ × Y) : 0 ≤ coneDistance x y := Real.sqrt_nonneg _

theorem coneDistance_comm (x y : ℝ × Y) : coneDistance x y = coneDistance y x := by
  unfold coneDistance
  rw [dist_comm y.2 x.2]
  congr 1
  ring

theorem coneDistance_same_direction (r s : ℝ) (u : Y) :
    coneDistance (r, u) (s, u) = |r - s| := by
  unfold coneDistance
  simp only [dist_self, min_eq_right Real.pi_pos.le, Real.cos_zero, mul_one]
  rw [show r ^ 2 + s ^ 2 - 2 * r * s = (r - s) ^ 2 by ring, Real.sqrt_sq_eq_abs]

theorem coneDistance_le_abs_sub_add_mul_dist {x y : ℝ × Y} {B : ℝ}
    (hx : x.1 ∈ Icc 0 B) (hy : y.1 ∈ Icc 0 B) :
    coneDistance x y ≤ |x.1 - y.1| + B * dist x.2 y.2 := by
  have hB : 0 ≤ B := hx.1.trans hx.2
  have htheta : 0 ≤ min Real.pi (dist x.2 y.2) := le_min Real.pi_pos.le dist_nonneg
  have hthetaSq := pow_le_pow_left₀ htheta (min_le_right Real.pi (dist x.2 y.2)) 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := min Real.pi (dist x.2 y.2))
  have hcosBound : 1 - dist x.2 y.2 ^ 2 / 2 ≤ Real.cos (min Real.pi (dist x.2 y.2)) := by
    linarith only [hthetaSq, hcos]
  have hab := mul_nonneg hx.1 hy.1
  have habB : x.1 * y.1 ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul hx.2 hy.2 hy.1 hB
  have hmul := mul_le_mul_of_nonneg_left hcosBound (show 0 ≤ 2 * x.1 * y.1 by nlinarith only [hab])
  have hbd := mul_le_mul_of_nonneg_right habB (sq_nonneg (dist x.2 y.2))
  unfold coneDistance
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hc := mul_nonneg (abs_nonneg (x.1 - y.1)) (mul_nonneg hB (dist_nonneg (x := x.2) (y := y.2)))
  nlinarith only [hmul, hbd, hc, sq_abs (x.1 - y.1)]

theorem coneDistance_sq {x y : ℝ × Y} (hx : 0 ≤ x.1) (hy : 0 ≤ y.1) :
    coneDistance x y ^ 2 =
      x.1 ^ 2 + y.1 ^ 2 - 2 * x.1 * y.1 * Real.cos (min Real.pi (dist x.2 y.2)) := by
  apply Real.sq_sqrt
  have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one (min Real.pi (dist x.2 y.2)))
    (show 0 ≤ 2 * x.1 * y.1 by positivity)
  nlinarith only [hh, sq_nonneg (x.1 - y.1)]

theorem coneDistance_recover_radius_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≠ b) (u : Y) {x : ℝ × Y} (hx : 0 ≤ x.1) :
    x.1 ^ 2 = a * b +
      (b * coneDistance (a, u) x ^ 2 - a * coneDistance (b, u) x ^ 2) / (b - a) := by
  rw [coneDistance_sq ha hx, coneDistance_sq hb hx]
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp
  ring

theorem continuous_coneDistance {Y : Type*} [PseudoMetricSpace Y] :
    Continuous (fun p : (ℝ × Y) × (ℝ × Y) => coneDistance p.1 p.2) := by
  unfold coneDistance
  fun_prop


theorem coneDistance_self {Y : Type*} [PseudoMetricSpace Y] (x : ℝ × Y) :
    coneDistance x x = 0 := by
  unfold coneDistance
  simp only [dist_self, min_eq_right Real.pi_pos.le, Real.cos_zero, mul_one]
  rw [show x.1 ^ 2 + x.1 ^ 2 - 2 * x.1 * x.1 = 0 by ring, Real.sqrt_zero]

theorem coneDistance_eq_zero_iff {Y : Type*} [MetricSpace Y] {x y : ℝ × Y}
    (hx : 0 < x.1) (hy : 0 < y.1) : coneDistance x y = 0 ↔ x = y := by
  refine ⟨fun hzero => ?_, fun h => h ▸ coneDistance_self x⟩
  have hsq := coneDistance_sq hx.le hy.le
  rw [hzero, zero_pow (by decide)] at hsq
  have hcos := Real.cos_le_one (min Real.pi (dist x.2 y.2))
  have hnonneg := mul_nonneg (show 0 ≤ 2 * x.1 * y.1 by positivity) (sub_nonneg.mpr hcos)
  have heq : x.1 = y.1 := by nlinarith only [hsq, hnonneg, sq_nonneg (x.1 - y.1)]
  have hangle : Real.cos (min Real.pi (dist x.2 y.2)) = 1 := by
    have hprod : 0 < 2 * x.1 * y.1 := by positivity
    have hz : (2 * x.1 * y.1) *
        (1 - Real.cos (min Real.pi (dist x.2 y.2))) = 0 := by nlinarith only [hsq, heq]
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hprod.ne')).symm
  have ht : min Real.pi (dist x.2 y.2) = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt
      (by linarith [le_min Real.pi_pos.le (dist_nonneg (x := x.2) (y := y.2)), Real.pi_pos])
      (by linarith [min_le_left Real.pi (dist x.2 y.2), Real.pi_pos])).mp hangle
  have hd : dist x.2 y.2 = 0 := by
    rcases min_cases Real.pi (dist x.2 y.2) with h | h
    · rw [h.1] at ht
      exact False.elim (Real.pi_pos.ne' ht)
    · rwa [h.1] at ht
  exact Prod.ext heq (dist_eq_zero.mp hd)

theorem abs_radius_sub_le_coneDistance {Y : Type*} [PseudoMetricSpace Y]
    {x y : ℝ × Y} (hx : 0 ≤ x.1) (hy : 0 ≤ y.1) :
    |x.1 - y.1| ≤ Metric.coneDistance x y := by
  have hs := Metric.coneDistance_sq hx hy
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one (min Real.pi (dist x.2 y.2)))
    (show 0 ≤ 2 * x.1 * y.1 by positivity)
  have hn := Metric.coneDistance_nonneg x y
  nlinarith only [hs, hc, hn, sq_abs (x.1 - y.1), abs_nonneg (x.1 - y.1)]

theorem dist_snd_eq_zero_of_coneDistance_le_radius_sub {Y : Type*} [PseudoMetricSpace Y]
    {z w : ℝ × Y} (hz : 0 < z.1) (hw : 0 < w.1)
    (hd : coneDistance z w ≤ w.1 - z.1) : dist z.2 w.2 = 0 := by
  have hrad : w.1 - z.1 ≤ coneDistance z w := by
    calc
      w.1 - z.1 ≤ |w.1 - z.1| := le_abs_self _
      _ = |z.1 - w.1| := abs_sub_comm _ _
      _ ≤ coneDistance z w := abs_radius_sub_le_coneDistance hz.le hw.le
  have heq : coneDistance z w = w.1 - z.1 := le_antisymm hd hrad
  have hs := coneDistance_sq hz.le hw.le
  rw [heq] at hs
  have hprod : (2 * z.1 * w.1) *
      (1 - Real.cos (min Real.pi (dist z.2 w.2))) = 0 := by
    nlinarith only [hs]
  have hcoef : 2 * z.1 * w.1 ≠ 0 := ne_of_gt (by positivity)
  have hcos : Real.cos (min Real.pi (dist z.2 w.2)) = 1 := by
    have h := (mul_eq_zero.mp hprod).resolve_left hcoef
    linarith only [h]
  have htheta : min Real.pi (dist z.2 w.2) = 0 := by
    apply (Real.cos_eq_one_iff_of_lt_of_lt ?_ ?_).mp hcos
    · exact lt_of_lt_of_le (by linarith [Real.pi_pos])
        (le_min Real.pi_pos.le dist_nonneg)
    · exact (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  rcases min_cases Real.pi (dist z.2 w.2) with h | h
  · rw [h.1] at htheta
    exact False.elim (Real.pi_pos.ne' htheta)
  · rwa [h.1] at htheta

theorem snd_eq_of_coneDistance_le_radius_sub {Y : Type*} [MetricSpace Y]
    {z w : ℝ × Y} (hz : 0 < z.1) (hw : 0 < w.1)
    (hd : coneDistance z w ≤ w.1 - z.1) : z.2 = w.2 :=
  dist_eq_zero.mp (dist_snd_eq_zero_of_coneDistance_le_radius_sub hz hw hd)

theorem coneDistance_radial_mul {Y : Type*} [PseudoMetricSpace Y]
    (c : ℝ) (x y : ℝ × Y) :
    coneDistance (c * x.1, x.2) (c * y.1, y.2) = |c| * coneDistance x y := by
  unfold coneDistance
  rw [show (c * x.1) ^ 2 + (c * y.1) ^ 2 -
      2 * (c * x.1) * (c * y.1) * Real.cos (min Real.pi (dist x.2 y.2)) =
      c ^ 2 * (x.1 ^ 2 + y.1 ^ 2 - 2 * x.1 * y.1 * Real.cos (min Real.pi (dist x.2 y.2))) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end Metric
