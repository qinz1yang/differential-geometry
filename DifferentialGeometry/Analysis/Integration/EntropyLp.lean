import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Integration


theorem abs_mul_log_le_one_add_rpow_div {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) :
    |x * Real.log x| ≤ 1 + x ^ (1 + δ) / δ := by
  have hpow : 0 ≤ x ^ (1 + δ) / δ :=
    div_nonneg (Real.rpow_nonneg hx _) hδ.le
  by_cases hx1 : x ≤ 1
  · rcases eq_or_lt_of_le hx with hx0 | hx0
    · simpa only [← hx0, zero_mul, abs_zero] using add_nonneg zero_le_one hpow
    · have hsmall : |x * Real.log x| < 1 := by
        simpa only [mul_comm] using Real.abs_log_mul_self_lt x hx0 hx1
      linarith
  · have hxpos : 0 < x := lt_trans zero_lt_one (lt_of_not_ge hx1)
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_not_ge hx1)
    rw [abs_of_nonneg (mul_nonneg hx hlog)]
    have hlarge := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx hδ) hx
    have hidentity : x * (x ^ δ / δ) = x ^ (1 + δ) / δ := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
      ring
    rw [hidentity] at hlarge
    linarith

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


theorem integrable_mul_log_of_memLp [IsFiniteMeasure μ]
    {f : α → ℝ} {q : ℝ} (hq : 1 < q)
    (hf : MemLp f (ENNReal.ofReal q) μ) (hf0 : 0 ≤ᵐ[μ] f) :
    Integrable (fun x => f x * Real.log (f x)) μ := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq.le
  have hmoment : Integrable (fun x => ‖f x‖ ^ q) μ := by
    simpa only [ENNReal.toReal_ofReal hq0] using hf.integrable_norm_rpow'
  have hbound : Integrable (fun x => 1 + ‖f x‖ ^ q / (q - 1)) μ :=
    (integrable_const (1 : ℝ)).add (hmoment.div_const (q - 1))
  refine hbound.mono'
    (Real.continuous_mul_log.comp_aestronglyMeasurable hf.aestronglyMeasurable) ?_
  filter_upwards [hf0] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx, show 1 + (q - 1) = q by ring]
    using abs_mul_log_le_one_add_rpow_div hx (sub_pos.mpr hq)


theorem integrable_sq_mul_log_sq_of_memLp [IsFiniteMeasure μ]
    {u : α → ℝ} {q : ℝ} (hq : 2 < q)
    (hu : MemLp u (ENNReal.ofReal q) μ) :
    Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) μ := by
  have hsq : MemLp (fun x => u x ^ 2) (ENNReal.ofReal (q / 2)) μ := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_ofNat, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      sq_abs] using hu.norm_rpow_div 2
  exact integrable_mul_log_of_memLp (by linarith : 1 < q / 2) hsq
    (Eventually.of_forall fun x => sq_nonneg (u x))


theorem abs_sq_mul_log_sq_le {q : ℝ} (hq : 2 < q) (u : ℝ) :
    |u ^ 2 * Real.log (u ^ 2)| ≤ 1 + ‖u‖ ^ q / (q / 2 - 1) := by
  have hb := abs_mul_log_le_one_add_rpow_div (sq_nonneg u)
    (by linarith : 0 < q / 2 - 1)
  have heq : (u ^ 2) ^ (1 + (q / 2 - 1)) = ‖u‖ ^ q := by
    rw [show 1 + (q / 2 - 1) = q / 2 by ring,
      show u ^ 2 = ‖u‖ ^ (2 : ℝ) by simp [Real.norm_eq_abs],
      ← Real.rpow_mul (norm_nonneg u), show (2 : ℝ) * (q / 2) = q by ring]
  simpa only [heq] using hb


theorem tendsto_integral_sq_mul_log_sq_of_dominated [IsFiniteMeasure μ]
    {q : ℝ} (hq : 2 < q) {u : ℕ → α → ℝ} {v b : α → ℝ}
    (hb : MemLp b (ENNReal.ofReal q) μ)
    (hu : ∀ n, AEStronglyMeasurable (u n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    Tendsto (fun n => ∫ x, u n x ^ 2 * Real.log (u n x ^ 2) ∂μ) atTop
      (𝓝 (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ)) := by
  have hq0 : 0 ≤ q := by linarith
  have hmoment : Integrable (fun x => ‖b x‖ ^ q) μ := by
    simpa only [ENNReal.toReal_ofReal hq0] using hb.integrable_norm_rpow'
  refine tendsto_integral_of_dominated_convergence
    (fun x => 1 + ‖b x‖ ^ q / (q / 2 - 1))
    (fun n => Real.continuous_mul_log.comp_aestronglyMeasurable ((hu n).pow 2))
    ((integrable_const (1 : ℝ)).add (hmoment.div_const _)) ?_ ?_
  · intro n
    filter_upwards [hbound n] with x hx
    rw [Real.norm_eq_abs]
    refine (abs_sq_mul_log_sq_le hq (u n x)).trans ?_
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ q / 2 - 1)
    exact Real.rpow_le_rpow (norm_nonneg _) (hx.trans (le_abs_self (b x))) hq0
  · filter_upwards [hlim] with x hx
    exact Real.continuous_mul_log.continuousAt.tendsto.comp (hx.pow 2)

end DifferentialGeometry.Analysis.Integration
