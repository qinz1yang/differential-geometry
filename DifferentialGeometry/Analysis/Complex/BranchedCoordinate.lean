import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private def powerQuotient (F : ℂ → ℂ) (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  if z = a then 1 else (n : ℂ) * (F z - F a) / (z - a) ^ n

private def powerRootFactor (F : ℂ → ℂ) (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.log (powerQuotient F a n z) / (n : ℂ))

private def powerCoordinate (F : ℂ → ℂ) (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (z - a) * powerRootFactor F a n z

private theorem powerCoordinate_eq (F : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    powerCoordinate F a n = fun z =>
      if z = a then 0 else
        (z - a) * Complex.exp
          (Complex.log ((n : ℂ) * (F z - F a) / (z - a) ^ n) / (n : ℂ)) := by
  funext z
  by_cases hza : z = a
  · subst z
    simp [powerCoordinate]
  · simp [powerCoordinate, powerRootFactor, powerQuotient, hza]

private theorem powerQuotient_bound {F : ℂ → ℂ} {a z : ℂ} {n : ℕ} {C : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C)
    (h : ‖F z - F a - (z - a) ^ n / (n : ℂ)‖ ≤ C * ‖z - a‖ ^ (n + 1)) :
    ‖powerQuotient F a n z - 1‖ ≤ (n : ℝ) * C * ‖z - a‖ := by
  by_cases hza : z = a
  · subst z
    have hz : powerQuotient F a n a - 1 = 0 := by simp [powerQuotient]
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hC) (norm_nonneg (a - a))
  have hw : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hp : 0 < ‖z - a‖ ^ n := pow_pos (norm_pos_iff.mpr hw) n
  have heq : powerQuotient F a n z - 1 =
      (n : ℂ) * (F z - F a - (z - a) ^ n / (n : ℂ)) / (z - a) ^ n := by
    simp only [powerQuotient, ite_eq_right hza]
    field_simp [hn0, hw]
  rw [heq, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
  apply (div_le_iff₀ hp).2
  calc
    (n : ℝ) * ‖F z - F a - (z - a) ^ n / (n : ℂ)‖ ≤
        (n : ℝ) * (C * ‖z - a‖ ^ (n + 1)) := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    _ = ((n : ℝ) * C * ‖z - a‖) * ‖z - a‖ ^ n := by rw [pow_succ]; ring

private theorem powerQuotient_continuousAt {F : ℂ → ℂ} {a : ℂ} {n : ℕ} {C R : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hR : 0 < R)
    (h : ∀ z ∈ ball a R,
      ‖F z - F a - (z - a) ^ n / (n : ℂ)‖ ≤ C * ‖z - a‖ ^ (n + 1)) :
    ContinuousAt (powerQuotient F a n) a := by
  have hz : Tendsto (fun z => powerQuotient F a n z - 1) (𝓝 a) (𝓝 0) := by
    apply squeeze_zero_norm'
      (Filter.eventually_of_mem (ball_mem_nhds a hR) fun z hz =>
        powerQuotient_bound hn hC (h z hz))
    have hnorm : ContinuousAt (fun z : ℂ => ‖z - a‖) a := by fun_prop
    simpa using (hnorm.const_mul ((n : ℝ) * C)).tendsto
  have hz' := hz.add_const (1 : ℂ)
  change Tendsto (powerQuotient F a n) (𝓝 a) (𝓝 (powerQuotient F a n a))
  rw [show powerQuotient F a n a = 1 by simp [powerQuotient]]
  simpa only [sub_add_cancel, zero_add] using hz'

private theorem powerQuotient_contDiffAt {F : ℂ → ℂ} {a z : ℂ} {n : ℕ}
    {k : WithTop ℕ∞} (hF : ContDiffAt ℝ k F z) (hza : z ≠ a) :
    ContDiffAt ℝ k (powerQuotient F a n) z := by
  have hw : (z - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
  have hq : ContDiffAt ℝ k
      (fun w => (n : ℂ) * (F w - F a) * ((w - a) ^ n)⁻¹) z :=
    (contDiffAt_const.mul (hF.sub contDiffAt_const)).mul
      (((contDiffAt_id.sub contDiffAt_const).pow n).inv hw)
  apply hq.congr_of_eventuallyEq
  filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hza] with w hw
  change w ≠ a at hw
  simp only [powerQuotient, ite_eq_right hw, div_eq_mul_inv]

private theorem powerCoordinate_contDiffAt {F : ℂ → ℂ} {a z : ℂ} {n : ℕ}
    {k : WithTop ℕ∞} (hF : ContDiffAt ℝ k F z) (hza : z ≠ a)
    (hq : powerQuotient F a n z ∈ Complex.slitPlane) :
    ContDiffAt ℝ k (powerCoordinate F a n) z := by
  have hlog : ContDiffAt ℝ k (fun w => Complex.log (powerQuotient F a n w)) z :=
    ((Complex.contDiffAt_log hq).restrict_scalars ℝ).comp z
      (powerQuotient_contDiffAt hF hza)
  have hroot : ContDiffAt ℝ k (powerRootFactor F a n) z := by
    exact Complex.contDiff_exp.contDiffAt.comp z (hlog.div_const (n : ℂ))
  exact (contDiffAt_id.sub contDiffAt_const).mul hroot

private theorem powerCoordinate_power {F : ℂ → ℂ} {a z : ℂ} {n : ℕ}
    (hn : 0 < n) (hq : powerQuotient F a n z ∈ Complex.slitPlane) :
    powerCoordinate F a n z ^ n = (n : ℂ) * (F z - F a) := by
  by_cases hza : z = a
  · subst z
    simp [powerCoordinate, Nat.ne_of_gt hn]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hw : (z - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
  have hroot : powerRootFactor F a n z ^ n = powerQuotient F a n z := by
    rw [powerRootFactor, ← Complex.exp_nat_mul]
    have hc : (n : ℂ) * (Complex.log (powerQuotient F a n z) / (n : ℂ)) =
        Complex.log (powerQuotient F a n z) := by field_simp
    rw [hc, Complex.exp_log (Complex.slitPlane_ne_zero hq)]
  rw [powerCoordinate, mul_pow, hroot, powerQuotient, ite_eq_right hza]
  field_simp

private theorem powerCoordinate_hasFDerivAt_center {F : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hQ : ContinuousAt (powerQuotient F a n) a) :
    HasFDerivAt (powerCoordinate F a n) (ContinuousLinearMap.id ℝ ℂ) a := by
  have hQa : powerQuotient F a n a = 1 := by simp [powerQuotient]
  have hK : ContinuousAt (powerRootFactor F a n) a := by
    have hlog : ContinuousAt (fun z => Complex.log (powerQuotient F a n z)) a :=
      (Complex.contDiffAt_log (n := 1) (by simp [hQa])).continuousAt.comp hQ
    exact Complex.continuous_exp.continuousAt.comp (hlog.div_const (n : ℂ))
  have hKa : powerRootFactor F a n a = 1 := by
    simp [powerRootFactor, powerQuotient]
  rw [hasFDerivAt_iff_tendsto]
  apply squeeze_zero' (Filter.Eventually.of_forall fun z =>
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  · exact Filter.Eventually.of_forall fun z => by
      change ‖z - a‖⁻¹ * ‖powerCoordinate F a n z -
        powerCoordinate F a n a - (z - a)‖ ≤ ‖powerRootFactor F a n z - 1‖
      have hfac : powerCoordinate F a n z - powerCoordinate F a n a - (z - a) =
          (z - a) * (powerRootFactor F a n z - 1) := by
        simp only [powerCoordinate, sub_self, zero_mul, sub_zero]
        ring
      rw [hfac, norm_mul, ← mul_assoc]
      by_cases hz : z - a = 0
      · simp [hz]
      · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz), one_mul]
  · simpa [hKa] using
      (hK.sub (continuousAt_const : ContinuousAt (fun _ : ℂ => (1 : ℂ)) a)).norm.tendsto

private def normalizedPowerDerivative (F : ℂ → ℂ) (a : ℂ) (n : ℕ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  if z = a then ContinuousLinearMap.id ℝ ℂ
  else ((z - a) ^ (n - 1))⁻¹ • fderiv ℝ F z

private theorem normalizedPowerDerivative_bound {F : ℂ → ℂ} {a z : ℂ} {n : ℕ} {C : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C)
    (h : ∀ v : ℂ, ‖fderiv ℝ F z v - (z - a) ^ (n - 1) * v‖ ≤
      C * ‖z - a‖ ^ n * ‖v‖) :
    ‖normalizedPowerDerivative F a n z - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖z - a‖ := by
  by_cases hza : z = a
  · subst z
    simp [normalizedPowerDerivative]
  have hw : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hwp : (z - a) ^ (n - 1) ≠ 0 := pow_ne_zero _ hw
  have hnorm : ‖z - a‖ ^ (n - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hw)
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _)) fun v => ?_
  have heq : (normalizedPowerDerivative F a n z - ContinuousLinearMap.id ℝ ℂ) v =
      ((z - a) ^ (n - 1))⁻¹ * (fderiv ℝ F z v - (z - a) ^ (n - 1) * v) := by
    simp only [normalizedPowerDerivative, ite_eq_right hza, sub_apply, smul_apply,
      smul_eq_mul]
    change ((z - a) ^ (n - 1))⁻¹ * fderiv ℝ F z v - v =
      ((z - a) ^ (n - 1))⁻¹ * (fderiv ℝ F z v - (z - a) ^ (n - 1) * v)
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hwp, one_mul]
  rw [heq, norm_mul, norm_inv, norm_pow]
  calc
    (‖z - a‖ ^ (n - 1))⁻¹ * ‖fderiv ℝ F z v - (z - a) ^ (n - 1) * v‖ ≤
        (‖z - a‖ ^ (n - 1))⁻¹ * (C * ‖z - a‖ ^ n * ‖v‖) :=
      mul_le_mul_of_nonneg_left (h v) (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _))
    _ = C * ‖z - a‖ * ‖v‖ := by
      have hn' : n = (n - 1) + 1 := (Nat.sub_add_cancel (Nat.succ_le_of_lt hn)).symm
      rw [show ‖z - a‖ ^ n = ‖z - a‖ ^ (n - 1) * ‖z - a‖ by
        conv_lhs => rw [hn', pow_succ]]
      calc
        (‖z - a‖ ^ (n - 1))⁻¹ * (C * (‖z - a‖ ^ (n - 1) * ‖z - a‖) * ‖v‖) =
            ((‖z - a‖ ^ (n - 1))⁻¹ * ‖z - a‖ ^ (n - 1)) * (C * ‖z - a‖ * ‖v‖) := by ring
        _ = C * ‖z - a‖ * ‖v‖ := by rw [inv_mul_cancel₀ hnorm, one_mul]

private theorem powerCoordinate_fderiv {F : ℂ → ℂ} {a z : ℂ} {n : ℕ} {R : ℝ}
    (hn : 0 < n) (hz : z ∈ ball a R) (hza : z ≠ a)
    (hF : ContDiffOn ℝ 1 F (ball a R))
    (hQ : ∀ w ∈ ball a R, powerQuotient F a n w ∈ Complex.slitPlane) :
    fderiv ℝ (powerCoordinate F a n) z =
      (powerRootFactor F a n z ^ (n - 1))⁻¹ • normalizedPowerDerivative F a n z := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hw : (z - a) ^ (n - 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
  have hK : powerRootFactor F a n z ^ (n - 1) ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  have hΨ := (powerCoordinate_contDiffAt (hF.contDiffAt (isOpen_ball.mem_nhds hz)) hza
    (hQ z hz)).differentiableAt_one.hasFDerivAt
  have hF' := ((hF.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt_one.hasFDerivAt.sub_const
    (F a)).const_mul (n : ℂ)
  have heq : (fun w => powerCoordinate F a n w ^ n) =ᶠ[𝓝 z]
      (fun w => (n : ℂ) * (F w - F a)) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw =>
      powerCoordinate_power hn (hQ w hw)
  have hder := (hΨ.pow n).unique (hF'.congr_of_eventuallyEq heq)
  ext v
  have hv := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hder
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul] at hv
  change fderiv ℝ (powerCoordinate F a n) z v = _
  simp only [normalizedPowerDerivative, ite_eq_right hza, smul_apply, smul_eq_mul]
  have hv' : powerCoordinate F a n z ^ (n - 1) *
      fderiv ℝ (powerCoordinate F a n) z v = fderiv ℝ F z v := by
    apply mul_left_cancel₀ hn0
    simpa only [mul_assoc] using hv
  rw [powerCoordinate, mul_pow] at hv'
  field_simp [hw, hK]
  linear_combination hv'

/-- The normalized positive-power quotient lies in the principal logarithm domain nearby. -/
theorem exists_ball_normalized_complex_power_mem_slitPlane
    {F : ℂ → ℂ} {a : ℂ} {n : ℕ} {C R : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hR : 0 < R)
    (hvalue : ∀ z ∈ Metric.ball a R,
      ‖F z - F a - (z - a) ^ n / (n : ℂ)‖ ≤ C * ‖z - a‖ ^ (n + 1)) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      ∀ z ∈ Metric.ball a r, z ≠ a →
        (n : ℂ) * (F z - F a) / (z - a) ^ n ∈ Complex.slitPlane := by
  have hQ := powerQuotient_continuousAt hn hC hR hvalue
  have hnear : ∀ᶠ z in 𝓝 a, powerQuotient F a n z ∈ Complex.slitPlane :=
    hQ.eventually (Complex.isOpen_slitPlane.mem_nhds (by simp [powerQuotient]))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min ε R / 2
  have hr : 0 < r := half_pos (lt_min hε hR)
  have hrε : r < ε := (half_lt_self (lt_min hε hR)).trans_le (min_le_left _ _)
  have hrR : r < R := (half_lt_self (lt_min hε hR)).trans_le (min_le_right _ _)
  refine ⟨r, hr, hrR, ?_⟩
  intro z hz hza
  have hq := hsub ((ball_subset_ball hrε.le) hz)
  change powerQuotient F a n z ∈ Complex.slitPlane at hq
  simpa only [powerQuotient, ite_eq_right hza] using hq

/-- Off the center, the literal principal-root coordinate inherits real regularity. -/
theorem contDiffAt_complex_power_root_coordinate
    {F : ℂ → ℂ} {a z : ℂ} {n : ℕ} {k : WithTop ℕ∞}
    (hF : ContDiffAt ℝ k F z) (hza : z ≠ a)
    (hQ : (n : ℂ) * (F z - F a) / (z - a) ^ n ∈ Complex.slitPlane) :
    ContDiffAt ℝ k
      (fun w : ℂ => if w = a then 0 else
        (w - a) * Complex.exp
          (Complex.log ((n : ℂ) * (F w - F a) / (w - a) ^ n) / (n : ℂ))) z := by
  have hq : powerQuotient F a n z ∈ Complex.slitPlane := by
    simpa only [powerQuotient, ite_eq_right hza] using hQ
  simpa only [powerCoordinate_eq] using powerCoordinate_contDiffAt hF hza hq

/-- A first-order perturbation of a positive complex power admits its literal local root coordinate. -/
theorem exists_c1_coordinate_of_complex_power_remainders
    {F : ℂ → ℂ} {a : ℂ} {n : ℕ} {Cv Cd R : ℝ}
    (hn : 0 < n) (hR : 0 < R) (hCv : 0 ≤ Cv) (hCd : 0 ≤ Cd)
    (hF : ContDiffOn ℝ 1 F (Metric.ball a R))
    (hvalue : ∀ z ∈ Metric.ball a R,
      ‖F z - F a - (z - a) ^ n / (n : ℂ)‖ ≤ Cv * ‖z - a‖ ^ (n + 1))
    (hderiv : ∀ z ∈ Metric.ball a R, ∀ v : ℂ,
      ‖fderiv ℝ F z v - (z - a) ^ (n - 1) * v‖ ≤
        Cd * ‖z - a‖ ^ n * ‖v‖) :
    let Ψ : ℂ → ℂ := fun z =>
      if z = a then 0 else
        (z - a) * Complex.exp
          (Complex.log ((n : ℂ) * (F z - F a) / (z - a) ^ n) / (n : ℂ))
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧
      ∃ e : OpenPartialHomeomorph ℂ ℂ,
        e.source = Metric.ball a ρ ∧
        (e : ℂ → ℂ) = Ψ ∧ e a = 0 ∧
        HasFDerivAt Ψ (ContinuousLinearMap.id ℝ ℂ) a ∧
        ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source ∧
        ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target ∧
        ∀ z ∈ e.source, F z = F a + Ψ z ^ n / (n : ℂ) := by
  rw [← powerCoordinate_eq F a n]
  let Ψ := powerCoordinate F a n
  change ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      e.source = ball a ρ ∧ (e : ℂ → ℂ) = Ψ ∧ e a = 0 ∧
      HasFDerivAt Ψ (ContinuousLinearMap.id ℝ ℂ) a ∧
      ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source ∧
      ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target ∧
      ∀ z ∈ e.source, F z = F a + Ψ z ^ n / (n : ℂ)
  have hQ := powerQuotient_continuousAt hn hCv hR hvalue
  have hQa : powerQuotient F a n a = 1 := by simp [powerQuotient]
  have hQnear : ∀ᶠ z in 𝓝 a, powerQuotient F a n z ∈ Complex.slitPlane :=
    hQ.eventually (Complex.isOpen_slitPlane.mem_nhds (by simp [hQa]))
  obtain ⟨s, hs, hsmall⟩ := Metric.mem_nhds_iff.mp
    (hQnear.and (ball_mem_nhds a hR))
  have hQs : ∀ z ∈ ball a s, powerQuotient F a n z ∈ Complex.slitPlane :=
    fun z hz => (hsmall hz).1
  have hFs : ContDiffOn ℝ 1 F (ball a s) := hF.mono fun _ hz => (hsmall hz).2
  have hΨa : Ψ a = 0 := by simp [Ψ, powerCoordinate]
  have hΨd : HasFDerivAt Ψ (ContinuousLinearMap.id ℝ ℂ) a :=
    powerCoordinate_hasFDerivAt_center hQ
  have hJ : ContinuousAt (normalizedPowerDerivative F a n) a := by
    have hz : Tendsto
        (fun z => normalizedPowerDerivative F a n z - ContinuousLinearMap.id ℝ ℂ)
        (𝓝 a) (𝓝 0) := by
      apply squeeze_zero_norm'
        (Filter.eventually_of_mem (ball_mem_nhds a hR) fun z hz =>
          normalizedPowerDerivative_bound hn hCd (hderiv z hz))
      have hnorm : ContinuousAt (fun z : ℂ => ‖z - a‖) a := by fun_prop
      simpa using (hnorm.const_mul Cd).tendsto
    have hz' := hz.add_const (ContinuousLinearMap.id ℝ ℂ)
    change Tendsto (normalizedPowerDerivative F a n) (𝓝 a)
      (𝓝 (normalizedPowerDerivative F a n a))
    rw [show normalizedPowerDerivative F a n a = ContinuousLinearMap.id ℝ ℂ by
      simp [normalizedPowerDerivative]]
    simpa only [sub_add_cancel, zero_add] using hz'
  have hK : ContinuousAt (powerRootFactor F a n) a := by
    have hlog : ContinuousAt (fun z => Complex.log (powerQuotient F a n z)) a :=
      (Complex.contDiffAt_log (n := 1) (by simp [hQa])).continuousAt.comp hQ
    exact Complex.continuous_exp.continuousAt.comp (hlog.div_const (n : ℂ))
  have hKa : powerRootFactor F a n a = 1 := by simp [powerRootFactor, powerQuotient]
  have hDcenter : ContinuousAt (fderiv ℝ Ψ) a := by
    have hA : ContinuousAt (fun z =>
        (powerRootFactor F a n z ^ (n - 1))⁻¹ • normalizedPowerDerivative F a n z) a :=
      ((hK.pow (n - 1)).inv₀ (by simp [hKa])).smul hJ
    apply hA.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds a hs] with z hz
    by_cases hza : z = a
    · subst z
      simp [hΨd.fderiv, hKa, normalizedPowerDerivative]
    · exact powerCoordinate_fderiv hn hz hza hFs hQs
  have hΨoff : ∀ z ∈ ball a s, z ≠ a → ContDiffAt ℝ 1 Ψ z :=
    fun z hz hza => powerCoordinate_contDiffAt
      (hFs.contDiffAt (isOpen_ball.mem_nhds hz)) hza (hQs z hz)
  have hΨC1 : ContDiffAt ℝ 1 Ψ a := by
    apply contDiffAt_one_iff.mpr
    refine ⟨fderiv ℝ Ψ, ball a s, ball_mem_nhds a hs, ?_, ?_⟩
    · intro z hz
      by_cases hza : z = a
      · subst z
        exact hDcenter.continuousWithinAt
      · exact ((hΨoff z hz hza).continuousAt_fderiv one_ne_zero).continuousWithinAt
    · intro z hz
      by_cases hza : z = a
      · subst z
        simpa [hΨd.fderiv] using hΨd
      · exact (hΨoff z hz hza).differentiableAt_one.hasFDerivAt
  let e₀ := hΨC1.toOpenPartialHomeomorph Ψ
    (f' := ContinuousLinearEquiv.refl ℝ ℂ) hΨd one_ne_zero
  have ha₀ : a ∈ e₀.source := hΨC1.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ ℂ) hΨd one_ne_zero
  have hInv : ContDiffAt ℝ 1 (e₀.symm : ℂ → ℂ) (Ψ a) :=
    hΨC1.to_localInverse (f' := ContinuousLinearEquiv.refl ℝ ℂ) hΨd one_ne_zero
  obtain ⟨u, hu, hCu⟩ := hΨC1.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hCv⟩ := hInv.contDiffOn le_rfl (by simp)
  have hnhds : ball a s ∩ e₀.source ∩ u ∩ Ψ ⁻¹' v ∈ 𝓝 a :=
    inter_mem (inter_mem (inter_mem (ball_mem_nhds a hs)
      (e₀.open_source.mem_nhds ha₀)) hu) (hΨd.continuousAt.preimage_mem_nhds hv)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let ρ := min ε R / 2
  have hρ : 0 < ρ := half_pos (lt_min hε hR)
  have hρε : ρ < ε := (half_lt_self (lt_min hε hR)).trans_le (min_le_left _ _)
  have hρR : ρ < R := (half_lt_self (lt_min hε hR)).trans_le (min_le_right _ _)
  have hb : ball a ρ ⊆ ball a s ∩ e₀.source ∩ u ∩ Ψ ⁻¹' v :=
    (ball_subset_ball hρε.le).trans hεsub
  let e := e₀.restrOpen (ball a ρ) isOpen_ball
  have hsource : e.source = ball a ρ := by
    change e₀.source ∩ ball a ρ = ball a ρ
    exact inter_eq_right.mpr fun z hz => (hb hz).1.1.2
  have hcoe : (e : ℂ → ℂ) = Ψ := rfl
  refine ⟨ρ, hρ, hρR, e, hsource, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcoe
  · exact hΨa
  · exact hΨd
  · rw [hcoe, hsource]
    exact hCu.mono fun z hz => (hb hz).1.2
  · change ContDiffOn ℝ 1 (e₀.symm : ℂ → ℂ) e.target
    apply hCv.mono
    intro y hy
    have hx : e.symm y ∈ ball a ρ := hsource ▸ e.map_target hy
    have hvy := (hb hx).2
    change e (e.symm y) ∈ v at hvy
    rwa [e.right_inv hy] at hvy
  · intro z hz
    change F z = F a + powerCoordinate F a n z ^ n / (n : ℂ)
    have hp := powerCoordinate_power hn (hQs z ((hb (hsource ▸ hz)).1.1.1))
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hd : F z - F a = powerCoordinate F a n z ^ n / (n : ℂ) := by
      apply (eq_div_iff hn0).2
      simpa only [mul_comm] using hp.symm
    rw [← hd]
    ring


private theorem normalizedPowerDerivative_factor
    {F : ℂ → ℂ} {T : ℂ → (ℂ →L[ℝ] ℂ)} {a z : ℂ} {n : ℕ}
    (hza : z ≠ a)
    (hDF : fderiv ℝ F z = (T z).comp
      ((z - a) ^ (n - 1) • ContinuousLinearMap.id ℝ ℂ)) :
    normalizedPowerDerivative F a n z = ContinuousLinearMap.id ℝ ℂ +
      ((z - a) ^ (n - 1))⁻¹ •
        ((T z - ContinuousLinearMap.id ℝ ℂ).comp
          ((z - a) ^ (n - 1) • ContinuousLinearMap.id ℝ ℂ)) := by
  have hp : (z - a) ^ (n - 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
  ext v
  simp only [normalizedPowerDerivative, ite_eq_right hza, hDF, smul_apply,
    ContinuousLinearMap.comp_apply, add_apply,
    sub_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  field_simp
  ring

private theorem root2_norm_smulRight_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : ℂ →L[ℝ] ℂ) (v : E) : ‖L.smulRight v‖ ≤ ‖L‖ * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro w
  change ‖L w • v‖ ≤ _
  calc
    ‖L w • v‖ = ‖L w‖ * ‖v‖ := norm_smul _ _
    _ ≤ (‖L‖ * ‖w‖) * ‖v‖ := mul_le_mul_of_nonneg_right (L.le_opNorm w) (norm_nonneg _)
    _ = (‖L‖ * ‖v‖) * ‖w‖ := by ring

private theorem root2_norm_fderiv_smul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] {c : ℂ → ℂ} {A : ℂ → E} {z : ℂ}
    (hc : DifferentiableAt ℝ c z) (hA : DifferentiableAt ℝ A z) :
    ‖fderiv ℝ (fun w => c w • A w) z‖ ≤
      ‖c z‖ * ‖fderiv ℝ A z‖ + ‖fderiv ℝ c z‖ * ‖A z‖ := by
  rw [fderiv_fun_smul hc hA]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_smul_le _ _) (root2_norm_smulRight_le _ _))

private theorem root2_norm_fderiv_clm_comp_le
    {A B : ℂ → (ℂ →L[ℝ] ℂ)} {z : ℂ}
    (hA : DifferentiableAt ℝ A z) (hB : DifferentiableAt ℝ B z) :
    ‖fderiv ℝ (fun w => (A w).comp (B w)) z‖ ≤
      ‖A z‖ * ‖fderiv ℝ B z‖ + ‖fderiv ℝ A z‖ * ‖B z‖ := by
  rw [fderiv_clm_comp hA hB]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    simpa using mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.norm_compL_le ℝ ℂ ℂ ℂ) (norm_nonneg (A z))
  · apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    calc
      ‖(ContinuousLinearMap.compL ℝ ℂ ℂ ℂ).flip (B z)‖ * ‖fderiv ℝ A z‖ ≤
          ‖B z‖ * ‖fderiv ℝ A z‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply (ContinuousLinearMap.le_opNorm _ _).trans
        simpa using mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.norm_compL_le ℝ ℂ ℂ ℂ)
          (norm_nonneg (B z))
      _ = ‖fderiv ℝ A z‖ * ‖B z‖ := mul_comm _ _

private theorem root2_power_derivatives {a z : ℂ} (m : ℕ) (hza : z ≠ a) :
    DifferentiableAt ℝ (fun w : ℂ => (w - a) ^ m) z ∧
    DifferentiableAt ℝ (fun w : ℂ => ((w - a) ^ m)⁻¹) z ∧
    ‖fderiv ℝ (fun w : ℂ => (w - a) ^ m) z‖ =
      (m : ℝ) * ‖z - a‖ ^ m / ‖z - a‖ ∧
    ‖fderiv ℝ (fun w : ℂ => ((w - a) ^ m)⁻¹) z‖ =
      (m : ℝ) / (‖z - a‖ ^ m * ‖z - a‖) := by
  have hs : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hr : ‖z - a‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  have hp : HasDerivAt (fun w : ℂ => (w - a) ^ m)
      ((m : ℂ) * (z - a) ^ (m - 1)) z := by
    convert ((hasDerivAt_id z).sub_const a).pow m using 1 <;> first | rfl | simp
  have hpR : HasFDerivAt (fun w : ℂ => (w - a) ^ m)
      (((m : ℂ) * (z - a) ^ (m - 1)) • ContinuousLinearMap.id ℝ ℂ) z := by
    convert hp.hasFDerivAt.restrictScalars ℝ using 1
    ext v
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  have hi := hp.inv (pow_ne_zero m hs)
  have hiR : HasFDerivAt (fun w : ℂ => ((w - a) ^ m)⁻¹)
      ((-((m : ℂ) * (z - a) ^ (m - 1)) / ((z - a) ^ m) ^ 2) •
        ContinuousLinearMap.id ℝ ℂ) z := by
    convert hi.hasFDerivAt.restrictScalars ℝ using 1
    ext v
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  refine ⟨hpR.differentiableAt, hiR.differentiableAt, ?_, ?_⟩
  · rw [hpR.fderiv, norm_smul, ContinuousLinearMap.norm_id, mul_one,
      norm_mul, Complex.norm_natCast, norm_pow]
    cases m with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel, pow_succ]; field_simp
  · simp only [hiR.fderiv, norm_smul, ContinuousLinearMap.norm_id, mul_one,
      norm_div, norm_neg, norm_mul, Complex.norm_natCast, norm_pow]
    cases m with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel, pow_succ]; field_simp

private theorem root2_normalizedPowerDerivative_derivative_bound
    {F : ℂ → ℂ} {T : ℂ → (ℂ →L[ℝ] ℂ)} {a z : ℂ} {n : ℕ} {C : ℝ}
    (hza : z ≠ a) (hC : 0 ≤ C) (hT : DifferentiableAt ℝ T z)
    (hsize : ‖T z - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖z - a‖)
    (hderiv : ‖fderiv ℝ T z‖ ≤ C)
    (hDF : ∀ᶠ w in 𝓝 z, fderiv ℝ F w = (T w).comp
      ((w - a) ^ (n - 1) • ContinuousLinearMap.id ℝ ℂ)) :
    DifferentiableAt ℝ (normalizedPowerDerivative F a n) z ∧
      ‖fderiv ℝ (normalizedPowerDerivative F a n) z‖ ≤
        (2 * (n - 1 : ℕ) + 1 : ℝ) * C := by
  let m := n - 1
  let c := fun w : ℂ => (w - a) ^ m
  let A := fun w => T w - ContinuousLinearMap.id ℝ ℂ
  let B := fun w => c w • ContinuousLinearMap.id ℝ ℂ
  let J := fun w => ContinuousLinearMap.id ℝ ℂ + (c w)⁻¹ • ((A w).comp (B w))
  obtain ⟨hc, hi, hdc, hdi⟩ := root2_power_derivatives m hza
  have hA : DifferentiableAt ℝ A z := hT.sub_const _
  have hB : DifferentiableAt ℝ B z := hc.smul_const _
  have hJ : DifferentiableAt ℝ J z := (hi.smul (hA.clm_comp hB)).const_add _
  have heq : normalizedPowerDerivative F a n =ᶠ[𝓝 z] J := by
    filter_upwards [hDF, (isOpen_ne_fun continuous_id continuous_const).mem_nhds hza]
      with w hw hwa
    exact normalizedPowerDerivative_factor hwa hw
  refine ⟨hJ.congr_of_eventuallyEq heq, ?_⟩
  rw [heq.fderiv_eq]
  change ‖fderiv ℝ (fun w => ContinuousLinearMap.id ℝ ℂ +
    (c w)⁻¹ • ((A w).comp (B w))) z‖ ≤ _
  rw [fderiv_const_add]
  have hDA : ‖fderiv ℝ A z‖ ≤ C := by simpa [A, fderiv_sub_const] using hderiv
  have hDB : ‖fderiv ℝ B z‖ ≤ (m : ℝ) * ‖z - a‖ ^ m / ‖z - a‖ := by
    rw [show B = (fun w => c w • ContinuousLinearMap.id ℝ ℂ) from rfl,
      fderiv_smul_const hc]
    simpa only [c, ContinuousLinearMap.norm_id, mul_one, hdc] using
      root2_norm_smulRight_le (fderiv ℝ c z) (ContinuousLinearMap.id ℝ ℂ)
  have hNB : ‖B z‖ = ‖z - a‖ ^ m := by simp [B, c, norm_smul, norm_pow]
  have hNI : ‖(c z)⁻¹‖ = (‖z - a‖ ^ m)⁻¹ := by simp [c, norm_inv, norm_pow]
  have hr : ‖z - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza)
  calc
    ‖fderiv ℝ (fun w => (c w)⁻¹ • ((A w).comp (B w))) z‖ ≤
        ‖(c z)⁻¹‖ * ‖fderiv ℝ (fun w => (A w).comp (B w)) z‖ +
          ‖fderiv ℝ (fun w => (c w)⁻¹) z‖ * ‖(A z).comp (B z)‖ :=
      root2_norm_fderiv_smul_le hi (hA.clm_comp hB)
    _ ≤ ‖(c z)⁻¹‖ * (‖A z‖ * ‖fderiv ℝ B z‖ + ‖fderiv ℝ A z‖ * ‖B z‖) +
          ‖fderiv ℝ (fun w => (c w)⁻¹) z‖ * (‖A z‖ * ‖B z‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (root2_norm_fderiv_clm_comp_le hA hB) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (‖z - a‖ ^ m)⁻¹ *
          ((C * ‖z - a‖) * ((m : ℝ) * ‖z - a‖ ^ m / ‖z - a‖) + C * ‖z - a‖ ^ m) +
          ((m : ℝ) / (‖z - a‖ ^ m * ‖z - a‖)) * ((C * ‖z - a‖) * ‖z - a‖ ^ m) := by
      rw [hNB, hNI, hdi]
      gcongr
    _ = (2 * (n - 1 : ℕ) + 1 : ℝ) * C := by
      dsimp [m]
      field_simp
      ring

private theorem root2_powerQuotient_derivative_bound
    {F : ℂ → ℂ} {a z : ℂ} {n : ℕ} {Cv Cd : ℝ}
    (hn : 0 < n) (hza : z ≠ a) (hCd : 0 ≤ Cd)
    (hF : DifferentiableAt ℝ F z)
    (hv : ‖F z - F a - (z - a) ^ n / (n : ℂ)‖ ≤ Cv * ‖z - a‖ ^ (n + 1))
    (hd : ∀ v : ℂ, ‖fderiv ℝ F z v - (z - a) ^ (n - 1) * v‖ ≤
      Cd * ‖z - a‖ ^ n * ‖v‖) :
    DifferentiableAt ℝ (powerQuotient F a n) z ∧
      ‖fderiv ℝ (powerQuotient F a n) z‖ ≤ (n : ℝ) * (Cd + (n : ℝ) * Cv) := by
  let H := fun w => F w - F a - (w - a) ^ n / (n : ℂ)
  let c := fun w : ℂ => ((w - a) ^ n)⁻¹
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hp : HasFDerivAt (fun w : ℂ => (w - a) ^ n / (n : ℂ))
      ((z - a) ^ (n - 1) • ContinuousLinearMap.id ℝ ℂ) z := by
    have hh := (((hasFDerivAt_id (𝕜 := ℝ) z).sub_const a).pow n).const_mul ((n : ℂ)⁻¹)
    convert hh using 1
    · funext w
      simp only [div_eq_inv_mul, id_eq]
    · ext v
      simp only [smul_apply, ContinuousLinearMap.id_apply, nsmul_eq_mul, smul_eq_mul, id_eq]
      field_simp
  have hH : HasFDerivAt H
      (fderiv ℝ F z - (z - a) ^ (n - 1) • ContinuousLinearMap.id ℝ ℂ) z := by
    exact (hF.hasFDerivAt.sub_const (F a)).sub hp
  have hDH : ‖fderiv ℝ H z‖ ≤ Cd * ‖z - a‖ ^ n := by
    rw [hH.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hCd (pow_nonneg (norm_nonneg _) _))
    intro v
    simpa only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using hd v
  obtain ⟨_, hc, _, hdc⟩ := root2_power_derivatives n hza
  have heq : powerQuotient F a n =ᶠ[𝓝 z] (fun w => 1 + (n : ℂ) * (c w * H w)) := by
    filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hza] with w hwa
    change w ≠ a at hwa
    dsimp [powerQuotient, H, c]
    rw [ite_eq_right hwa]
    field_simp [pow_ne_zero n (sub_ne_zero.mpr hwa)]
    ring
  have hq : DifferentiableAt ℝ (fun w => 1 + (n : ℂ) * (c w * H w)) z :=
    ((hc.mul hH.differentiableAt).const_mul _).const_add _
  refine ⟨hq.congr_of_eventuallyEq heq, ?_⟩
  rw [heq.fderiv_eq, fderiv_const_add]
  have he : (fun w => (n : ℂ) * (c w * H w)) = (fun w => (n : ℂ) • (c w • H w)) := rfl
  rw [he]
  have hsmul := ((hc.smul hH.differentiableAt).hasFDerivAt.const_smul (n : ℂ)).fderiv
  change fderiv ℝ (fun w => (n : ℂ) • (c w • H w)) z =
    (n : ℂ) • fderiv ℝ (fun w => c w • H w) z at hsmul
  rw [hsmul, norm_smul, Complex.norm_natCast]
  have hr : ‖z - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  calc
    ‖fderiv ℝ (fun w => c w • H w) z‖ ≤
        ‖c z‖ * ‖fderiv ℝ H z‖ + ‖fderiv ℝ c z‖ * ‖H z‖ :=
      root2_norm_fderiv_smul_le hc hH.differentiableAt
    _ ≤ (‖z - a‖ ^ n)⁻¹ * (Cd * ‖z - a‖ ^ n) +
        ((n : ℝ) / (‖z - a‖ ^ n * ‖z - a‖)) * (Cv * ‖z - a‖ ^ (n + 1)) := by
      have hcN : ‖c z‖ = (‖z - a‖ ^ n)⁻¹ := by simp [c, norm_inv, norm_pow]
      change ‖c z‖ * ‖fderiv ℝ H z‖ +
        ‖fderiv ℝ (fun w : ℂ => ((w - a) ^ n)⁻¹) z‖ * ‖H z‖ ≤ _
      rw [hcN, hdc]
      gcongr
    _ = Cd + (n : ℝ) * Cv := by rw [pow_succ]; field_simp

/-- The literal normalized root coordinate has bounded actual second derivative off the
center when the original derivative has a `C¹` real-linear coefficient. -/
theorem exists_bounded_second_fderiv_complex_power_root_coordinate
    {F : ℂ → ℂ} {T : ℂ → (ℂ →L[ℝ] ℂ)} {a : ℂ} {n : ℕ} {Cv Cd R : ℝ}
    (hn : 0 < n) (hR : 0 < R) (hCv : 0 ≤ Cv) (hCd : 0 ≤ Cd)
    (hF : ContDiffOn ℝ 1 F (ball a R))
    (hT : ContDiffOn ℝ 1 T (ball a R))
    (hTa : T a = ContinuousLinearMap.id ℝ ℂ)
    (hDF : ∀ z ∈ ball a R, z ≠ a → fderiv ℝ F z = (T z).comp
      ((z - a) ^ (n - 1) • ContinuousLinearMap.id ℝ ℂ))
    (hvalue : ∀ z ∈ ball a R,
      ‖F z - F a - (z - a) ^ n / (n : ℂ)‖ ≤ Cv * ‖z - a‖ ^ (n + 1))
    (hderiv : ∀ z ∈ ball a R, ∀ v : ℂ,
      ‖fderiv ℝ F z v - (z - a) ^ (n - 1) * v‖ ≤ Cd * ‖z - a‖ ^ n * ‖v‖) :
    let Ψ := fun z : ℂ => if z = a then 0 else
      (z - a) * Complex.exp
        (Complex.log ((n : ℂ) * (F z - F a) / (z - a) ^ n) / (n : ℂ))
    ∃ r C : ℝ, 0 < r ∧ r < R ∧ 0 < C ∧
      ∀ z ∈ ball a r, z ≠ a →
        DifferentiableAt ℝ (fderiv ℝ Ψ) z ∧ ‖fderiv ℝ (fderiv ℝ Ψ) z‖ ≤ C := by
  let A := fun q : ℂ =>
    (Complex.exp (Complex.log q / (n : ℂ)) ^ (n - 1))⁻¹
  have hA : ContDiffAt ℝ 1 A 1 := by
    have hlog : ContDiffAt ℝ 1 Complex.log 1 :=
      (Complex.contDiffAt_log (by simp)).restrict_scalars ℝ
    exact ((Complex.contDiff_exp.contDiffAt.comp 1 (hlog.div_const (n : ℂ))).pow
      (n - 1)).inv (pow_ne_zero _ (Complex.exp_ne_zero _))
  let B : ℝ := ‖A 1‖ + 1
  let D : ℝ := ‖fderiv ℝ A 1‖ + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hAb : ∀ᶠ q in 𝓝 (1 : ℂ), ‖A q‖ < B :=
    hA.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [B]; linarith))
  have hDAb : ∀ᶠ q in 𝓝 (1 : ℂ), ‖fderiv ℝ A q‖ < D :=
    (hA.continuousAt_fderiv one_ne_zero).norm.eventually
      (gt_mem_nhds (by dsimp [D]; linarith))
  have hQ := powerQuotient_continuousAt hn hCv hR hvalue
  have hQa : powerQuotient F a n a = 1 := by simp [powerQuotient]
  have hQ1 : Tendsto (powerQuotient F a n) (𝓝 a) (𝓝 (1 : ℂ)) := hQa ▸ hQ
  have hTc := hT.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  obtain ⟨K, S, hS, hLip⟩ := hTc.exists_lipschitzOnWith
  let C₀ : ℝ := max (K : ℝ) (‖fderiv ℝ T a‖ + 1)
  have hC₀ : 0 ≤ C₀ := le_trans K.coe_nonneg (le_max_left _ _)
  have hDT : ∀ᶠ z in 𝓝 a, ‖fderiv ℝ T z‖ < ‖fderiv ℝ T a‖ + 1 :=
    (hTc.continuousAt_fderiv one_ne_zero).norm.eventually (gt_mem_nhds (by linarith))
  have hnear : ∀ᶠ z in 𝓝 a,
      z ∈ ball a R ∧ z ∈ ball a 1 ∧ z ∈ S ∧
      ‖fderiv ℝ T z‖ ≤ C₀ ∧
      powerQuotient F a n z ∈ Complex.slitPlane ∧
      DifferentiableAt ℝ A (powerQuotient F a n z) ∧
      ‖A (powerQuotient F a n z)‖ ≤ B ∧
      ‖fderiv ℝ A (powerQuotient F a n z)‖ ≤ D := by
    filter_upwards [ball_mem_nhds a hR, ball_mem_nhds a zero_lt_one, hS, hDT,
      hQ1.eventually (Complex.isOpen_slitPlane.mem_nhds (by simp)),
      hQ1.eventually (hA.eventually (by simp)), hQ1.eventually hAb, hQ1.eventually hDAb]
      with z hzR hz1 hzS hzDT hzQ hzA hzB hzD
    exact ⟨hzR, hz1, hzS, hzDT.le.trans (le_max_right _ _), hzQ,
      hzA.differentiableAt_one, hzB.le, hzD.le⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min ε R / 2
  have hr : 0 < r := half_pos (lt_min hε hR)
  have hrε : r < ε := (half_lt_self (lt_min hε hR)).trans_le (min_le_left _ _)
  have hrR : r < R := (half_lt_self (lt_min hε hR)).trans_le (min_le_right _ _)
  have hsub : ∀ z ∈ ball a r,
      z ∈ ball a R ∧ z ∈ ball a 1 ∧ z ∈ S ∧
      ‖fderiv ℝ T z‖ ≤ C₀ ∧
      powerQuotient F a n z ∈ Complex.slitPlane ∧
      DifferentiableAt ℝ A (powerQuotient F a n z) ∧
      ‖A (powerQuotient F a n z)‖ ≤ B ∧
      ‖fderiv ℝ A (powerQuotient F a n z)‖ ≤ D :=
    fun z hz => hεsub ((ball_subset_ball hrε.le) hz)
  let Q : ℝ := (n : ℝ) * (Cd + (n : ℝ) * Cv)
  let M : ℝ := (2 * (n - 1 : ℕ) + 1 : ℝ) * C₀
  have hQnonneg : 0 ≤ Q := by dsimp [Q]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨r, B * M + (D * Q) * (Cd + 1) + 1, hr, hrR, by positivity, ?_⟩
  intro z hz hza
  obtain ⟨hzR, hz1, hzS, hzDT, _, hzA, hzB, hzD⟩ := hsub z hz
  have hTsize : ‖T z - ContinuousLinearMap.id ℝ ℂ‖ ≤ C₀ * ‖z - a‖ := by
    rw [← hTa]
    exact (hLip.norm_sub_le hzS (mem_of_mem_nhds hS)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hDFe : ∀ᶠ w in 𝓝 z, fderiv ℝ F w = (T w).comp
      ((w - a) ^ (n - 1) • ContinuousLinearMap.id ℝ ℂ) := by
    filter_upwards [isOpen_ball.mem_nhds hzR,
      (isOpen_ne_fun continuous_id continuous_const).mem_nhds hza] with w hw hwa
    exact hDF w hw hwa
  obtain ⟨hJ, hDJ⟩ := root2_normalizedPowerDerivative_derivative_bound hza hC₀
    (hT.contDiffAt (isOpen_ball.mem_nhds hzR)).differentiableAt_one hTsize hzDT hDFe
  obtain ⟨hq, hDq⟩ := root2_powerQuotient_derivative_bound hn hza hCd
    (hF.contDiffAt (isOpen_ball.mem_nhds hzR)).differentiableAt_one
    (hvalue z hzR) (hderiv z hzR)
  have hJnorm : ‖normalizedPowerDerivative F a n z‖ ≤ Cd + 1 := by
    calc
      ‖normalizedPowerDerivative F a n z‖ ≤
          ‖normalizedPowerDerivative F a n z - ContinuousLinearMap.id ℝ ℂ‖ +
            ‖ContinuousLinearMap.id ℝ ℂ‖ := norm_le_norm_sub_add _ _
      _ ≤ Cd * ‖z - a‖ + 1 := by
        simpa only [ContinuousLinearMap.norm_id] using
          add_le_add (normalizedPowerDerivative_bound hn hCd (hderiv z hzR)) (le_refl (1 : ℝ))
      _ ≤ Cd + 1 := by
        have hzN : ‖z - a‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz1
        nlinarith
  have hc : DifferentiableAt ℝ (fun w => A (powerQuotient F a n w)) z := hzA.comp z hq
  have hDc : ‖fderiv ℝ (fun w => A (powerQuotient F a n w)) z‖ ≤ D * Q := by
    change ‖fderiv ℝ (A ∘ powerQuotient F a n) z‖ ≤ D * Q
    rw [fderiv_comp z hzA hq]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hzD hDq (norm_nonneg _) hD)
  have heq : fderiv ℝ (powerCoordinate F a n) =ᶠ[𝓝 z]
      (fun w => A (powerQuotient F a n w) • normalizedPowerDerivative F a n w) := by
    filter_upwards [isOpen_ball.mem_nhds hz,
      (isOpen_ne_fun continuous_id continuous_const).mem_nhds hza] with w hw hwa
    exact powerCoordinate_fderiv hn hw hwa (hF.mono (ball_subset_ball hrR.le))
      (fun v hv => (hsub v hv).2.2.2.2.1)
  have hdiff := (hc.smul hJ).congr_of_eventuallyEq heq
  have hbound : ‖fderiv ℝ (fderiv ℝ (powerCoordinate F a n)) z‖ ≤
      B * M + (D * Q) * (Cd + 1) := by
    rw [heq.fderiv_eq]
    exact (root2_norm_fderiv_smul_le hc hJ).trans
      (add_le_add (mul_le_mul hzB hDJ (norm_nonneg _) hB)
        (mul_le_mul hDc hJnorm (norm_nonneg _) (mul_nonneg hD hQnonneg)))
  simpa only [powerCoordinate_eq] using
    And.intro hdiff (hbound.trans (le_add_of_nonneg_right zero_le_one))

end DifferentialGeometry.Analysis
