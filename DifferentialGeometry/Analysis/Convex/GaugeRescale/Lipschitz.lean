import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Tactic.Module

noncomputable section

open Metric Set
open scoped NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem abs_ratio_sub_ratio_bound {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    |a / b - c / d| ≤ |a - c| / b + |c| * |d - b| / (b * d) := by
  have heq : a / b - c / d = (a - c) / b + c * (d - b) / (b * d) := by
    field_simp
    ring
  rw [heq]
  apply (abs_add_le _ _).trans_eq
  rw [abs_div, abs_of_pos hb, abs_div, abs_mul, abs_mul,
    abs_of_pos hb, abs_of_pos hd]

theorem lipschitzWith_gaugeRescale_from_unitBall
    {s : Set E} {r R : ℝ≥0} (hc : Convex ℝ s) (hr : 0 < r) (hR : 0 < R)
    (hin : ball (0 : E) r ⊆ s) (hout : s ⊆ closedBall (0 : E) R) :
    LipschitzWith (2 * R + R ^ 2 / r) (gaugeRescale (ball (0 : E) 1) s) := by
  have hga : Absorbent ℝ s := (absorbent_ball_zero hr).mono hin
  have hg := hc.lipschitzWith_gauge hr hin
  have hlow (x : E) : ‖x‖ / (R : ℝ) ≤ gauge s x :=
    le_gauge_of_subset_closedBall hga R.coe_nonneg hout
  have hratio (x : E) (hx : x ≠ 0) : ‖x‖ / gauge s x ≤ R := by
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hgpos : 0 < gauge s x := (div_pos hxpos hR).trans_le (hlow x)
    apply (div_le_iff₀ hgpos).mpr
    have h := (div_le_iff₀ (show 0 < (R : ℝ) from hR)).mp (hlow x)
    simpa only [mul_comm] using h
  have hordered (x y : E) (hxy : ‖y‖ ≤ ‖x‖) :
      dist (gaugeRescale (ball (0 : E) 1) s x) (gaugeRescale (ball (0 : E) 1) s y) ≤
        (2 * (R : ℝ) + (R : ℝ) ^ 2 / r) * dist x y := by
    by_cases hy : y = 0
    · subst y
      by_cases hx : x = 0
      · subst x
        simp
      have hb := hratio x hx
      have hc0 : (R : ℝ) ≤ 2 * R + (R : ℝ) ^ 2 / r := by
        nlinarith [R.coe_nonneg, div_nonneg (sq_nonneg (R : ℝ)) r.coe_nonneg]
      rw [gaugeRescale_zero, dist_zero_right, gaugeRescale, gauge_unit_ball, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (gauge_nonneg _))]
      simpa only [dist_zero_right] using (mul_le_mul_of_nonneg_right hb (norm_nonneg x)).trans
        (mul_le_mul_of_nonneg_right hc0 (norm_nonneg x))
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hxpos : 0 < ‖x‖ := hypos.trans_le hxy
    have hgx : 0 < gauge s x := (div_pos hxpos hR).trans_le (hlow x)
    have hgy : 0 < gauge s y := (div_pos hypos hR).trans_le (hlow y)
    have hRx := hratio x (norm_pos_iff.mp hxpos)
    have hRy := hratio y hy
    have hRy' : ‖y‖ / gauge s x ≤ R :=
      (div_le_div_of_nonneg_right hxy hgx.le).trans hRx
    have hnorm : |‖x‖ - ‖y‖| ≤ dist x y := by
      simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y
    have hgdiff : |gauge s y - gauge s x| ≤ (r : ℝ)⁻¹ * dist x y := by
      simpa only [Real.dist_eq, NNReal.coe_inv, abs_sub_comm] using hg.dist_le_mul x y
    have hcoef : |‖x‖ / gauge s x - ‖y‖ / gauge s y| * ‖y‖ ≤
        ((R : ℝ) + (R : ℝ) ^ 2 / r) * dist x y := by
      calc
        _ ≤ (|‖x‖ - ‖y‖| / gauge s x +
            ‖y‖ * |gauge s y - gauge s x| / (gauge s x * gauge s y)) * ‖y‖ := by
          have h := abs_ratio_sub_ratio_bound (a := ‖x‖) (c := ‖y‖) hgx hgy
          rw [abs_of_pos hypos] at h
          exact mul_le_mul_of_nonneg_right h hypos.le
        _ = (‖y‖ / gauge s x) * |‖x‖ - ‖y‖| +
            (‖y‖ / gauge s x) * (‖y‖ / gauge s y) * |gauge s y - gauge s x| := by ring
        _ ≤ (R : ℝ) * dist x y + (R : ℝ) * R * ((r : ℝ)⁻¹ * dist x y) := by
          apply add_le_add
          · exact mul_le_mul hRy' hnorm (abs_nonneg _) R.coe_nonneg
          · apply mul_le_mul _ hgdiff (abs_nonneg _) (mul_nonneg R.coe_nonneg R.coe_nonneg)
            exact mul_le_mul hRy' hRy (div_nonneg hypos.le hgy.le) R.coe_nonneg
        _ = _ := by ring
    have heq : gaugeRescale (ball (0 : E) 1) s x - gaugeRescale (ball (0 : E) 1) s y =
        (‖x‖ / gauge s x) • (x - y) +
          (‖x‖ / gauge s x - ‖y‖ / gauge s y) • y := by
      simp only [gaugeRescale, gauge_unit_ball]
      module
    rw [dist_eq_norm, heq]
    calc
      _ ≤ ‖(‖x‖ / gauge s x) • (x - y)‖ +
          ‖(‖x‖ / gauge s x - ‖y‖ / gauge s y) • y‖ := norm_add_le _ _
      _ = (‖x‖ / gauge s x) * dist x y +
          |‖x‖ / gauge s x - ‖y‖ / gauge s y| * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hxpos.le hgx.le), dist_eq_norm]
      _ ≤ (R : ℝ) * dist x y + ((R : ℝ) + (R : ℝ) ^ 2 / r) * dist x y :=
        add_le_add (mul_le_mul_of_nonneg_right hRx dist_nonneg) hcoef
      _ = _ := by ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h : dist (gaugeRescale (ball (0 : E) 1) s x) (gaugeRescale (ball (0 : E) 1) s y) ≤
      (2 * (R : ℝ) + (R : ℝ) ^ 2 / r) * dist x y := by
    by_cases hxy : ‖y‖ ≤ ‖x‖
    · exact hordered x y hxy
    · simpa only [dist_comm] using hordered y x (le_of_not_ge hxy)
  simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow,
    NNReal.coe_div] using h

theorem lipschitzWith_gaugeRescale_to_unitBall
    {s : Set E} {r : ℝ≥0} (hc : Convex ℝ s) (hr : 0 < r)
    (hin : ball (0 : E) r ⊆ s) :
    LipschitzWith (3 / r) (gaugeRescale s (ball (0 : E) 1)) := by
  have hg := hc.lipschitzWith_gauge hr hin
  have hupper (x : E) : gauge s x ≤ (r : ℝ)⁻¹ * ‖x‖ := by
    have h := hg.dist_le_mul x 0
    simpa only [gauge_zero, dist_zero_right, Real.norm_eq_abs, Real.dist_eq, sub_zero,
      abs_of_nonneg (gauge_nonneg _), NNReal.coe_inv] using h
  have hratio (x : E) (hx : 0 < ‖x‖) : gauge s x / ‖x‖ ≤ (r : ℝ)⁻¹ :=
    (div_le_iff₀ hx).mpr (hupper x)
  have hordered (x y : E) (hxy : ‖y‖ ≤ ‖x‖) :
      dist (gaugeRescale s (ball (0 : E) 1) x) (gaugeRescale s (ball (0 : E) 1) y) ≤
        (3 / (r : ℝ)) * dist x y := by
    by_cases hy : y = 0
    · subst y
      by_cases hx : x = 0
      · subst x
        simp
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [gaugeRescale_zero, dist_zero_right, gaugeRescale, gauge_unit_ball, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (div_nonneg (gauge_nonneg _) hxpos.le),
        div_mul_cancel₀ _ hxpos.ne']
      apply (hupper x).trans
      have hr0 : 0 < (r : ℝ) := hr
      have hc0 : (r : ℝ)⁻¹ ≤ 3 / r := by
        rw [inv_eq_one_div]
        exact div_le_div_of_nonneg_right (by norm_num) hr0.le
      simpa only [dist_zero_right] using mul_le_mul_of_nonneg_right hc0 (norm_nonneg x)
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hxpos : 0 < ‖x‖ := hypos.trans_le hxy
    have hnorm : |‖y‖ - ‖x‖| ≤ dist x y := by
      simpa only [dist_eq_norm, abs_sub_comm] using abs_norm_sub_norm_le x y
    have hgdiff : |gauge s x - gauge s y| ≤ (r : ℝ)⁻¹ * dist x y := by
      simpa only [Real.dist_eq, NNReal.coe_inv] using hg.dist_le_mul x y
    have hRy : ‖y‖ / ‖x‖ ≤ 1 := (div_le_one hxpos).mpr hxy
    have hgy : gauge s y / ‖x‖ ≤ (r : ℝ)⁻¹ := by
      apply (div_le_iff₀ hxpos).mpr
      exact (hupper y).trans (mul_le_mul_of_nonneg_left hxy (by positivity))
    have hcoef : |gauge s x / ‖x‖ - gauge s y / ‖y‖| * ‖y‖ ≤
        (2 / (r : ℝ)) * dist x y := by
      calc
        _ ≤ (|gauge s x - gauge s y| / ‖x‖ +
            gauge s y * |‖y‖ - ‖x‖| / (‖x‖ * ‖y‖)) * ‖y‖ := by
          have h := abs_ratio_sub_ratio_bound (a := gauge s x) (c := gauge s y) hxpos hypos
          rw [abs_of_nonneg (gauge_nonneg _)] at h
          exact mul_le_mul_of_nonneg_right h hypos.le
        _ = (‖y‖ / ‖x‖) * |gauge s x - gauge s y| +
            (gauge s y / ‖x‖) * |‖y‖ - ‖x‖| := by
          field_simp
        _ ≤ 1 * ((r : ℝ)⁻¹ * dist x y) + (r : ℝ)⁻¹ * dist x y :=
          add_le_add (mul_le_mul hRy hgdiff (abs_nonneg _) zero_le_one)
            (mul_le_mul hgy hnorm (abs_nonneg _) (by positivity))
        _ = _ := by ring
    have heq : gaugeRescale s (ball (0 : E) 1) x - gaugeRescale s (ball (0 : E) 1) y =
        (gauge s x / ‖x‖) • (x - y) +
          (gauge s x / ‖x‖ - gauge s y / ‖y‖) • y := by
      simp only [gaugeRescale, gauge_unit_ball]
      module
    rw [dist_eq_norm, heq]
    calc
      _ ≤ ‖(gauge s x / ‖x‖) • (x - y)‖ +
          ‖(gauge s x / ‖x‖ - gauge s y / ‖y‖) • y‖ := norm_add_le _ _
      _ = (gauge s x / ‖x‖) * dist x y +
          |gauge s x / ‖x‖ - gauge s y / ‖y‖| * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (gauge_nonneg _) hxpos.le), dist_eq_norm]
      _ ≤ (r : ℝ)⁻¹ * dist x y + (2 / (r : ℝ)) * dist x y :=
        add_le_add (mul_le_mul_of_nonneg_right (hratio x hxpos) dist_nonneg) hcoef
      _ = _ := by ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h : dist (gaugeRescale s (ball (0 : E) 1) x) (gaugeRescale s (ball (0 : E) 1) y) ≤
      (3 / (r : ℝ)) * dist x y := by
    by_cases hxy : ‖y‖ ≤ ‖x‖
    · exact hordered x y hxy
    · simpa only [dist_comm] using hordered y x (le_of_not_ge hxy)
  simpa only [NNReal.coe_div, NNReal.coe_ofNat] using h

end DifferentialGeometry.Analysis

end
