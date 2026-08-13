import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

theorem norm_sq_div_add_inner_ge_neg_quarter_norm_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {alpha : ℝ} (halpha : 0 < alpha) (p v : V) :
    -(alpha / 4) * ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 / alpha + inner ℝ p v := by
  have hinner : -(‖p‖ * ‖v‖) ≤ inner ℝ p v :=
    neg_le_of_abs_le (abs_real_inner_le_norm p v)
  have haux : -(alpha / 4) * ‖v‖ ^ 2 - inner ℝ p v ≤
      ‖p‖ ^ 2 / alpha := by
    apply (le_div_iff₀ halpha).2
    nlinarith [sq_nonneg (‖p‖ - alpha * ‖v‖ / 2)]
  linarith

theorem endpoint_difference_le_intervalIntegral_of_derivative_lower_bound
    {phi derivative bound : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hderivative : ContinuousOn derivative (Icc a b))
    (hbound : ContinuousOn bound (Icc a b))
    (hphi : ∀ t ∈ Icc a b, HasDerivAt phi (derivative t) t)
    (hlower : ∀ t ∈ Icc a b, -bound t ≤ derivative t) :
    phi a - phi b ≤ ∫ t in a..b, bound t := by
  have hderivative_uIcc : ContinuousOn derivative (uIcc a b) := by
    simpa [uIcc_of_le hab] using hderivative
  have hbound_uIcc : ContinuousOn bound (uIcc a b) := by
    simpa [uIcc_of_le hab] using hbound
  have hderivative_int : IntervalIntegrable derivative volume a b :=
    hderivative_uIcc.intervalIntegrable
  have hbound_int : IntervalIntegrable bound volume a b :=
    hbound_uIcc.intervalIntegrable
  have hftc : (∫ t in a..b, derivative t) = phi b - phi a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hphi t (by simpa [uIcc_of_le hab] using ht))
      hderivative_int
  have hmono : (∫ t in a..b, -bound t) ≤ ∫ t in a..b, derivative t :=
    intervalIntegral.integral_mono_on hab hbound_int.neg
      hderivative_int hlower
  rw [intervalIntegral.integral_neg, hftc] at hmono
  linarith

theorem harnack_endpoint_of_log_derivative_lower_bound
    {u logDerivative bound : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hu : ∀ t ∈ Icc a b, 0 < u t)
    (hlogDerivative : ContinuousOn logDerivative (Icc a b))
    (hbound : ContinuousOn bound (Icc a b))
    (hlog : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => Real.log (u s)) (logDerivative t) t)
    (hlower : ∀ t ∈ Icc a b, -bound t ≤ logDerivative t) :
    u a ≤ Real.exp (∫ t in a..b, bound t) * u b := by
  have hlog_bound : Real.log (u a) - Real.log (u b) ≤
      ∫ t in a..b, bound t :=
    endpoint_difference_le_intervalIntegral_of_derivative_lower_bound
      hab hlogDerivative hbound hlog hlower
  have hua : 0 < u a := hu a ⟨le_rfl, hab⟩
  have hub : 0 < u b := hu b ⟨hab, le_rfl⟩
  have hle : Real.log (u a) ≤
      (∫ t in a..b, bound t) + Real.log (u b) := by
    linarith
  have hexp := (Real.log_le_iff_le_exp hua).mp hle
  rw [Real.exp_add, Real.exp_log hub] at hexp
  exact hexp

theorem harnack_endpoint_of_derivative_lower_bound
    {u derivative bound : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hu : ∀ t ∈ Icc a b, 0 < u t)
    (hderivative : ContinuousOn derivative (Icc a b))
    (hbound : ContinuousOn bound (Icc a b))
    (hu_deriv : ∀ t ∈ Icc a b, HasDerivAt u (derivative t) t)
    (hlower : ∀ t ∈ Icc a b, -bound t ≤ derivative t / u t) :
    u a ≤ Real.exp (∫ t in a..b, bound t) * u b := by
  have hu_cont : ContinuousOn u (Icc a b) := by
    intro t ht
    exact (hu_deriv t ht).continuousAt.continuousWithinAt
  have hratio : ContinuousOn (fun t => derivative t / u t) (Icc a b) :=
    hderivative.div hu_cont (fun t ht => (hu t ht).ne')
  apply harnack_endpoint_of_log_derivative_lower_bound
    hab hu hratio hbound
  · intro t ht
    exact (hu_deriv t ht).log (hu t ht).ne'
  · exact hlower

theorem harnack_endpoint_of_derivative_lower_bound_with_time_pole
    {u derivative error : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ t ∈ Icc a b, 0 < u t)
    (hderivative : ContinuousOn derivative (Icc a b))
    (herror : ContinuousOn error (Icc a b))
    (hu_deriv : ∀ t ∈ Icc a b, HasDerivAt u (derivative t) t)
    (hlower : ∀ t ∈ Icc a b,
      -(c / t + error t) ≤ derivative t / u t) :
    u a ≤ (b / a) ^ c * Real.exp (∫ t in a..b, error t) * u b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hdiv : ContinuousOn (fun t : ℝ => c / t) (Icc a b) :=
    continuousOn_const.div continuousOn_id
      (fun t ht => (lt_of_lt_of_le ha ht.1).ne')
  have htotal : ContinuousOn (fun t => c / t + error t) (Icc a b) :=
    hdiv.add herror
  have hmain := harnack_endpoint_of_derivative_lower_bound
    hab hu hderivative htotal hu_deriv hlower
  have hdiv_uIcc : ContinuousOn (fun t : ℝ => c / t) (uIcc a b) := by
    simpa [uIcc_of_le hab] using hdiv
  have herror_uIcc : ContinuousOn error (uIcc a b) := by
    simpa [uIcc_of_le hab] using herror
  have hdiv_int : IntervalIntegrable (fun t : ℝ => c / t) volume a b :=
    hdiv_uIcc.intervalIntegrable
  have herror_int : IntervalIntegrable error volume a b :=
    herror_uIcc.intervalIntegrable
  have hintegral : (∫ t in a..b, c / t + error t) =
      c * Real.log (b / a) + ∫ t in a..b, error t := by
    rw [intervalIntegral.integral_add hdiv_int herror_int]
    have hrewrite : (fun t : ℝ => c / t) = fun t => c * (1 / t) := by
      funext t
      ring
    rw [hrewrite, intervalIntegral.integral_const_mul,
      integral_one_div_of_pos ha hb]
  rw [hintegral, Real.exp_add] at hmain
  have hratio : 0 < b / a := div_pos hb ha
  rw [show Real.exp (c * Real.log (b / a)) = (b / a) ^ c by
    rw [Real.rpow_def_of_pos hratio]
    congr 1
    ring] at hmain
  exact hmain

theorem harnack_endpoint_of_derivative_lower_bound_with_time_pole_and_constant
    {u derivative : ℝ → ℝ} {a b c K : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ t ∈ Icc a b, 0 < u t)
    (hderivative : ContinuousOn derivative (Icc a b))
    (hu_deriv : ∀ t ∈ Icc a b, HasDerivAt u (derivative t) t)
    (hlower : ∀ t ∈ Icc a b,
      -(c / t + K) ≤ derivative t / u t) :
    u a ≤ (b / a) ^ c * Real.exp (K * (b - a)) * u b := by
  have hmain := harnack_endpoint_of_derivative_lower_bound_with_time_pole
    (u := u) (derivative := derivative) (error := fun _ => K)
    ha hab hu hderivative continuousOn_const hu_deriv hlower
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hmain

theorem harnack_endpoint_of_li_yau_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u derivative timePart : ℝ → ℝ} {gradient velocity : ℝ → V}
    {a b c alpha : ℝ}
    (halpha : 0 < alpha) (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ t ∈ Icc a b, 0 < u t)
    (hderivative : ContinuousOn derivative (Icc a b))
    (hvelocity : ContinuousOn velocity (Icc a b))
    (hu_deriv : ∀ t ∈ Icc a b, HasDerivAt u (derivative t) t)
    (hpath : ∀ t ∈ Icc a b, derivative t / u t =
      timePart t + inner ℝ (gradient t) (velocity t))
    (hliYau : ∀ t ∈ Icc a b,
      -(c / t) + ‖gradient t‖ ^ 2 / alpha ≤ timePart t) :
    u a ≤ (b / a) ^ c *
      Real.exp (∫ t in a..b, alpha / 4 * ‖velocity t‖ ^ 2) * u b := by
  apply harnack_endpoint_of_derivative_lower_bound_with_time_pole
    (u := u) (derivative := derivative)
    (error := fun t => alpha / 4 * ‖velocity t‖ ^ 2)
    ha hab hu hderivative
  · exact continuousOn_const.mul (hvelocity.norm.pow 2)
  · exact hu_deriv
  · intro t ht
    rw [hpath t ht]
    have hyoung := norm_sq_div_add_inner_ge_neg_quarter_norm_sq
      halpha (gradient t) (velocity t)
    nlinarith [hliYau t ht]

theorem harnack_endpoint_of_li_yau_bound_abstract
    {u derivative timePart gradSq innerGV speedSq : ℝ → ℝ} {a b c alpha : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ t ∈ Icc a b, 0 < u t)
    (hderivative : ContinuousOn derivative (Icc a b))
    (hspeed : ContinuousOn speedSq (Icc a b))
    (hu_deriv : ∀ t ∈ Icc a b, HasDerivAt u (derivative t) t)
    (hpath : ∀ t ∈ Icc a b, derivative t / u t = timePart t + innerGV t)
    (hliYau : ∀ t ∈ Icc a b, -(c / t) + gradSq t / alpha ≤ timePart t)
    (hquad : ∀ t ∈ Icc a b, -(alpha / 4) * speedSq t ≤ gradSq t / alpha + innerGV t) :
    u a ≤ (b / a) ^ c * Real.exp (∫ t in a..b, alpha / 4 * speedSq t) * u b := by
  apply harnack_endpoint_of_derivative_lower_bound_with_time_pole
    (u := u) (derivative := derivative)
    (error := fun t => alpha / 4 * speedSq t)
    ha hab hu hderivative
  · exact continuousOn_const.mul hspeed
  · exact hu_deriv
  · intro t ht
    rw [hpath t ht]
    have hly := hliYau t ht
    have hq := hquad t ht
    nlinarith

end DifferentialGeometry.Analysis.Parabolic.Harnack

end
