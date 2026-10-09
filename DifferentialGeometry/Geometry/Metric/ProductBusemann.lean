import DifferentialGeometry.Geometry.Metric.Approximation.ProductCollapse
import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

namespace Real

theorem sqrt_sq_add_sq_sub_bounds {u r B T : ℝ}
    (hu : |u| ≤ B) (hqr : u ^ 2 + r ^ 2 ≤ B ^ 2) (hTB : B < T) :
    0 ≤ sqrt ((T - u) ^ 2 + r ^ 2) - (T - u) ∧
      sqrt ((T - u) ^ 2 + r ^ 2) - (T - u) ≤ B ^ 2 / (2 * (T - B)) := by
  have ha : 0 < T - u := by linarith [(abs_le.mp hu).2]
  have hs := sq_sqrt (show 0 ≤ (T - u) ^ 2 + r ^ 2 by positivity)
  have hn := sqrt_nonneg ((T - u) ^ 2 + r ^ 2)
  have hlow : 0 ≤ sqrt ((T - u) ^ 2 + r ^ 2) - (T - u) := by
    nlinarith [sq_nonneg r]
  refine ⟨hlow, (le_div_iff₀ (by linarith : 0 < 2 * (T - B))).mpr ?_⟩
  have hden : 2 * (T - B) ≤ sqrt ((T - u) ^ 2 + r ^ 2) + (T - u) := by
    linarith [(abs_le.mp hu).2]
  have hm := mul_le_mul_of_nonneg_left hden hlow
  nlinarith [sq_nonneg u]

end Real

namespace WithLp

variable {Y : Type*} [MetricSpace Y]

theorem dist_real_axis_sub_bounds (x : WithLp 2 (ℝ × Y)) (b : Y) {B T : ℝ}
    (hB : dist x (toLp 2 ((0 : ℝ), b)) ≤ B) (hTB : B < T) :
    0 ≤ dist x (toLp 2 (T, b)) - T + x.fst ∧
      dist x (toLp 2 (T, b)) - T + x.fst ≤ B ^ 2 / (2 * (T - B)) := by
  have hu : |x.fst| ≤ B := by
    have hh := (dist_fst_le x (toLp 2 ((0 : ℝ), b))).trans hB
    change dist x.fst (0 : ℝ) ≤ B at hh
    simpa only [Real.dist_eq, sub_zero] using hh
  have hsq : x.fst ^ 2 + dist x.snd b ^ 2 = dist x (toLp 2 ((0 : ℝ), b)) ^ 2 := by
    have hh := (prod_dist_sq_eq_add_sq x (toLp 2 ((0 : ℝ), b))).symm
    change dist x.fst (0 : ℝ) ^ 2 + dist x.snd b ^ 2 = _ at hh
    simpa only [Real.dist_eq, sub_zero, sq_abs] using hh
  have hqr : x.fst ^ 2 + dist x.snd b ^ 2 ≤ B ^ 2 := by
    rw [hsq]
    exact pow_le_pow_left₀ dist_nonneg hB 2
  have hp : dist x (toLp 2 (T, b)) = Real.sqrt ((T - x.fst) ^ 2 + dist x.snd b ^ 2) := by
    rw [prod_dist_eq_sqrt_sq_add_sq]
    change Real.sqrt (dist x.fst T ^ 2 + dist x.snd b ^ 2) = _
    simp only [Real.dist_eq, sq_abs]
    congr 1
    ring
  have he : dist x (toLp 2 (T, b)) - T + x.fst =
      Real.sqrt ((T - x.fst) ^ 2 + dist x.snd b ^ 2) - (T - x.fst) := by rw [hp]; ring
  rw [he]
  exact Real.sqrt_sq_add_sq_sub_bounds hu hqr hTB

theorem dist_negative_real_axis_sub_bounds (x : WithLp 2 (ℝ × Y)) (b : Y) {B T : ℝ}
    (hB : dist x (toLp 2 ((0 : ℝ), b)) ≤ B) (hTB : B < T) :
    0 ≤ dist x (toLp 2 (-T, b)) - T - x.fst ∧
      dist x (toLp 2 (-T, b)) - T - x.fst ≤ B ^ 2 / (2 * (T - B)) := by
  let y : WithLp 2 (ℝ × Y) := toLp 2 (-x.fst, x.snd)
  have hzero : dist y (toLp 2 ((0 : ℝ), b)) = dist x (toLp 2 ((0 : ℝ), b)) := by
    simp only [prod_dist_eq_sqrt_sq_add_sq]
    change Real.sqrt (dist (-x.fst) (0 : ℝ) ^ 2 + dist x.snd b ^ 2) =
      Real.sqrt (dist x.fst (0 : ℝ) ^ 2 + dist x.snd b ^ 2)
    simp only [Real.dist_eq, sub_zero, sq_abs, neg_sq]
  have hneg : dist y (toLp 2 (T, b)) = dist x (toLp 2 (-T, b)) := by
    simp only [prod_dist_eq_sqrt_sq_add_sq]
    change Real.sqrt (dist (-x.fst) T ^ 2 + dist x.snd b ^ 2) =
      Real.sqrt (dist x.fst (-T) ^ 2 + dist x.snd b ^ 2)
    rw [← dist_neg_neg x.fst (-T), neg_neg]
  have hy : dist y (toLp 2 ((0 : ℝ), b)) ≤ B := hzero.trans_le hB
  have hh := dist_real_axis_sub_bounds y b hy hTB
  rw [hneg] at hh
  change 0 ≤ dist x (toLp 2 (-T, b)) - T + -x.fst ∧
    dist x (toLp 2 (-T, b)) - T + -x.fst ≤ B ^ 2 / (2 * (T - B)) at hh
  simpa only [sub_eq_add_neg] using hh

theorem tendsto_dist_real_axis_sub (x : WithLp 2 (ℝ × Y)) (b : Y) :
    Tendsto (fun T : ℝ => dist x (toLp 2 (T, b)) - T) atTop (𝓝 (-x.fst)) := by
  let B := dist x (toLp 2 ((0 : ℝ), b))
  have hsub : Tendsto (fun T : ℝ => T - B) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-B) tendsto_id
  have hden : Tendsto (fun T : ℝ => 2 * (T - B)) atTop atTop :=
    hsub.const_mul_atTop (by norm_num)
  have hbound : Tendsto (fun T : ℝ => B ^ 2 / (2 * (T - B))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hden).const_mul (B ^ 2)
  have herr : Tendsto (fun T : ℝ => dist x (toLp 2 (T, b)) - T + x.fst) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hbound
    · filter_upwards [eventually_gt_atTop B] with T hT
      exact (dist_real_axis_sub_bounds x b (le_refl B) hT).1
    · filter_upwards [eventually_gt_atTop B] with T hT
      exact (dist_real_axis_sub_bounds x b (le_refl B) hT).2
  simpa only [add_sub_cancel_right, zero_sub] using herr.sub_const x.fst

end WithLp

namespace IsometryEquiv

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem dist_aligned_line_sub_bounds (e : X ≃ᵢ WithLp 2 (ℝ × Y)) {γ : ℝ → X} {b : Y}
    (halign : ∀ t, e (γ t) = WithLp.toLp 2 (t, b))
    (x : X) {B T : ℝ} (hB : dist x (γ 0) ≤ B) (hTB : B < T) :
    (0 ≤ dist x (γ T) - T + (e x).fst ∧
      dist x (γ T) - T + (e x).fst ≤ B ^ 2 / (2 * (T - B))) ∧
    (0 ≤ dist x (γ (-T)) - T - (e x).fst ∧
      dist x (γ (-T)) - T - (e x).fst ≤ B ^ 2 / (2 * (T - B))) := by
  have hb : dist (e x) (WithLp.toLp 2 ((0 : ℝ), b)) ≤ B := by
    rwa [← halign 0, e.dist_eq]
  have hp := WithLp.dist_real_axis_sub_bounds (e x) b hb hTB
  have hn := WithLp.dist_negative_real_axis_sub_bounds (e x) b hb hTB
  rw [← halign T, e.dist_eq] at hp
  rw [← halign (-T), e.dist_eq] at hn
  exact ⟨hp, hn⟩

theorem tendsto_dist_aligned_line_sub (e : X ≃ᵢ WithLp 2 (ℝ × Y)) {γ : ℝ → X} {b : Y}
    (halign : ∀ t, e (γ t) = WithLp.toLp 2 (t, b)) (x : X) :
    Tendsto (fun T : ℝ => dist x (γ T) - T) atTop (𝓝 (-(e x).fst)) := by
  have hfun : (fun T : ℝ => dist x (γ T) - T) =
      (fun T : ℝ => dist (e x) (WithLp.toLp 2 (T, b)) - T) := by
    funext T
    rw [← halign T, e.dist_eq]
  rw [hfun]
  exact WithLp.tendsto_dist_real_axis_sub (e x) b

theorem eventually_abs_dist_aligned_line_sub_lt
    (e : X ≃ᵢ WithLp 2 (ℝ × Y)) {γ : ℝ → X} {b : Y}
    (halign : ∀ t, e (γ t) = WithLp.toLp 2 (t, b)) (B : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ x : X, dist x (γ 0) ≤ B →
      |dist x (γ T) - T + (e x).fst| < η ∧
      |dist x (γ (-T)) - T - (e x).fst| < η := by
  have hsub : Tendsto (fun T : ℝ => T - B) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-B) tendsto_id
  have hden : Tendsto (fun T : ℝ => 2 * (T - B)) atTop atTop :=
    hsub.const_mul_atTop (by norm_num)
  have hbound : Tendsto (fun T : ℝ => B ^ 2 / (2 * (T - B))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hden).const_mul (B ^ 2)
  filter_upwards [eventually_gt_atTop B, hbound.eventually (eventually_lt_nhds hη)] with T hT ht
  intro x hx
  obtain ⟨hp, hn⟩ := e.dist_aligned_line_sub_bounds halign x hx hT
  rw [abs_of_nonneg hp.1, abs_of_nonneg hn.1]
  exact ⟨hp.2.trans_lt ht, hn.2.trans_lt ht⟩

end IsometryEquiv
