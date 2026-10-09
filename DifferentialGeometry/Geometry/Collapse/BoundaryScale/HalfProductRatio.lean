import DifferentialGeometry.Geometry.Collapse.CuspBoundary
import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The half-product volume ratio is monotone (route R3, statement M, one-dimensional kernel)

For the boundary comparison Q of route R3 the flat model volume of a half ball in `T² × [0, ∞)`
centred at height `z₁ ≥ 0` is `F(r) = ∫_{max(-r,-z₁)}^r A(√(r² - y²)) dy`, where `A(s)` is the area of
the flat-torus ball of radius `s`. If `A ≥ 0` is monotone and `A(s)/s²` is antitone on `(0, ∞)` (the
2D Bishop–Gromov for the flat torus), then `F(r)/r³` is antitone on `(0, ∞)`.
Proof: the substitution `y = r t` gives
`F(r)/r³ = ∫_{max(-1,-z₁/r)}^1 A(r√(1-t²))/r² dt`; the lower limit increases with `r` (as `z₁ ≥ 0`),
the integrand is nonnegative and, pointwise, `A(rc)/r² = c² A(rc)/(rc)²` decreases in `r`. No
injectivity radius and no lower bound on `z₁` beyond `0` is needed.
The torus form (`torus_halfBall_div_cube_antitone_of_area_ratio`) takes `A` to be the actual
`g_T`-ball area; the geometric lane supplies its area-ratio hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- The rescaled slice integrand `t ↦ A(r √(1 - t²))` is interval integrable for monotone
nonnegative `A` and `r ≥ 0` (it is measurable and bounded by `A r`). -/
theorem intervalIntegrable_comp_mul_sqrt_one_sub_sq {A : ℝ → ℝ} (hA0 : ∀ s, 0 ≤ A s)
    (hAmono : Monotone A) {r : ℝ} (hr : 0 ≤ r) (a c : ℝ) :
    IntervalIntegrable (fun t => A (r * Real.sqrt (1 - t ^ 2))) volume a c := by
  rw [intervalIntegrable_iff]
  have hcont : Continuous fun t : ℝ => r * Real.sqrt (1 - t ^ 2) :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2)))
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    (hAmono.measurable.comp hcont.measurable).aestronglyMeasurable (A r) ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hA0 _)]
  apply hAmono
  have hle : Real.sqrt (1 - t ^ 2) ≤ 1 :=
    (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])).trans_eq Real.sqrt_one
  exact mul_le_of_le_one_right hr hle

/-- The substitution `y = r t` in the half-ball slice integral. -/
theorem integral_halfBall_slices_eq_mul (A : ℝ → ℝ) {z₁ r : ℝ} (hr : 0 < r) :
    (∫ y in max (-r) (-z₁)..r, A (Real.sqrt (r ^ 2 - y ^ 2))) =
      r * ∫ t in max (-1) (-(z₁ / r))..1, A (r * Real.sqrt (1 - t ^ 2)) := by
  have hc : r ≠ 0 := hr.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := max (-1) (-(z₁ / r))) (b := 1)
    (fun y => A (Real.sqrt (r ^ 2 - y ^ 2))) hc
  have hend : r * max (-1) (-(z₁ / r)) = max (-r) (-z₁) := by
    rw [mul_max_of_nonneg _ _ hr.le]
    congr 1
    · ring
    · field_simp
  rw [hend, mul_one, smul_eq_mul] at h
  have hcongr : (∫ t in max (-1) (-(z₁ / r))..1, A (Real.sqrt (r ^ 2 - (r * t) ^ 2))) =
      ∫ t in max (-1) (-(z₁ / r))..1, A (r * Real.sqrt (1 - t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [show r ^ 2 - (r * t) ^ 2 = r ^ 2 * (1 - t ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  rw [← hcongr, h, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- Pointwise step: `A(b c)/b² ≤ A(s c)/s²` for `0 < s ≤ b`, `c ≥ 0`, from the area ratio. -/
theorem div_sq_le_div_sq_of_area_ratio {A : ℝ → ℝ} (hA0 : ∀ s, 0 ≤ A s)
    (hratio : ∀ s b : ℝ, 0 < s → s ≤ b → A b / b ^ 2 ≤ A s / s ^ 2) {s b c : ℝ} (hs : 0 < s)
    (hsb : s ≤ b) (hc : 0 ≤ c) :
    A (b * c) / b ^ 2 ≤ A (s * c) / s ^ 2 := by
  have hb : 0 < b := hs.trans_le hsb
  rcases hc.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero, mul_zero]
    exact div_le_div_of_nonneg_left (hA0 0) (pow_pos hs 2) (pow_le_pow_left₀ hs.le hsb 2)
  · have h := hratio (s * c) (b * c) (mul_pos hs hpos) (mul_le_mul_of_nonneg_right hsb hc)
    have hb0 : b ≠ 0 := hb.ne'
    have hs0 : s ≠ 0 := hs.ne'
    have hc0 : c ≠ 0 := hpos.ne'
    have e1 : A (b * c) / b ^ 2 = c ^ 2 * (A (b * c) / (b * c) ^ 2) := by
      field_simp
    have e2 : A (s * c) / s ^ 2 = c ^ 2 * (A (s * c) / (s * c) ^ 2) := by
      field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h (sq_nonneg c)

/-- M, one-dimensional kernel: a nonnegative monotone `A` with antitone `A(s)/s²` on `(0, ∞)` has
antitone half-ball ratio `F(r)/r³`, `F(r) = ∫_{max(-r,-z₁)}^r A(√(r² - y²)) dy`, for every `z₁ ≥ 0`. -/
theorem halfBall_slice_integral_div_cube_antitone {A : ℝ → ℝ} (hA0 : ∀ s, 0 ≤ A s)
    (hAmono : Monotone A) (hratio : ∀ s b : ℝ, 0 < s → s ≤ b → A b / b ^ 2 ≤ A s / s ^ 2)
    {z₁ s b : ℝ} (hz₁ : 0 ≤ z₁) (hs : 0 < s) (hsb : s ≤ b) :
    (∫ y in max (-b) (-z₁)..b, A (Real.sqrt (b ^ 2 - y ^ 2))) / b ^ 3 ≤
      (∫ y in max (-s) (-z₁)..s, A (Real.sqrt (s ^ 2 - y ^ 2))) / s ^ 3 := by
  have hb : 0 < b := hs.trans_le hsb
  have hred : ∀ r : ℝ, 0 < r →
      (∫ y in max (-r) (-z₁)..r, A (Real.sqrt (r ^ 2 - y ^ 2))) / r ^ 3 =
        ∫ t in max (-1) (-(z₁ / r))..1, A (r * Real.sqrt (1 - t ^ 2)) / r ^ 2 := by
    intro r hr
    rw [integral_halfBall_slices_eq_mul A hr, intervalIntegral.integral_div]
    have hr0 : r ≠ 0 := hr.ne'
    field_simp
  rw [hred b hb, hred s hs]
  have hint : ∀ r : ℝ, 0 < r → ∀ a c : ℝ,
      IntervalIntegrable (fun t => A (r * Real.sqrt (1 - t ^ 2)) / r ^ 2) volume a c :=
    fun r hr a c => (intervalIntegrable_comp_mul_sqrt_one_sub_sq hA0 hAmono hr.le a c).div_const _
  have has_ab : max (-1) (-(z₁ / s)) ≤ max (-1) (-(z₁ / b)) :=
    max_le_max le_rfl (neg_le_neg (div_le_div_of_nonneg_left hz₁ hs hsb))
  have hab1 : max (-1) (-(z₁ / b)) ≤ 1 :=
    max_le (by norm_num) (by have := div_nonneg hz₁ hb.le; linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint s hs (max (-1) (-(z₁ / s))) (max (-1) (-(z₁ / b)))) (hint s hs (max (-1) (-(z₁ / b))) 1)
  have hnonneg : 0 ≤ ∫ t in max (-1) (-(z₁ / s))..max (-1) (-(z₁ / b)),
      A (s * Real.sqrt (1 - t ^ 2)) / s ^ 2 :=
    intervalIntegral.integral_nonneg has_ab fun t _ => div_nonneg (hA0 _) (sq_nonneg s)
  have hmono : (∫ t in max (-1) (-(z₁ / b))..1, A (b * Real.sqrt (1 - t ^ 2)) / b ^ 2) ≤
      ∫ t in max (-1) (-(z₁ / b))..1, A (s * Real.sqrt (1 - t ^ 2)) / s ^ 2 :=
    intervalIntegral.integral_mono_on hab1 (hint b hb _ _) (hint s hs _ _) fun t _ =>
      div_sq_le_div_sq_of_area_ratio hA0 hratio hs hsb (Real.sqrt_nonneg _)
  linarith

/-- Consumer (torus form, the plug for the geometric lane): with `A` the area of the balls of the
flat torus `g_T` of a hyperbolic cusp in its OWN distance, an area-ratio bound (2D Bishop–Gromov)
gives the antitone half-ball ratio `F(r)/r³` at every height `z₁ ≥ 0`. -/
theorem torus_halfBall_div_cube_antitone_of_area_ratio (Hc : HyperbolicCusp) (x : Torus)
    (hratio : ∀ s b : ℝ, 0 < s → s ≤ b →
      (ballVolume Hc.torusMetric x b).toReal / b ^ 2 ≤ (ballVolume Hc.torusMetric x s).toReal / s ^ 2)
    {z₁ s b : ℝ} (hz₁ : 0 ≤ z₁) (hs : 0 < s) (hsb : s ≤ b) :
    (∫ y in max (-b) (-z₁)..b, (ballVolume Hc.torusMetric x (Real.sqrt (b ^ 2 - y ^ 2))).toReal) /
        b ^ 3 ≤
      (∫ y in max (-s) (-z₁)..s, (ballVolume Hc.torusMetric x (Real.sqrt (s ^ 2 - y ^ 2))).toReal) /
        s ^ 3 := by
  let : MeasurableSpace Torus := borel Torus
  have hfin := Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    (I := torusModel) (M := Torus) Hc.torusMetric
  have hmono : Monotone fun r : ℝ => (ballVolume Hc.torusMetric x r).toReal := by
    intro r t hrt
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_lt_ofReal_monotone _ (riemannianEDistOf Hc.torusMetric x) hrt)
  exact halfBall_slice_integral_div_cube_antitone (fun _ => ENNReal.toReal_nonneg) hmono hratio
    hz₁ hs hsb

end DifferentialGeometry.Geometry.Collapse
