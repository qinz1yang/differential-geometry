import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis

theorem ofReal_mul_log_le_lintegral_of_reciprocal_lower_bound
    {f : ℝ → ℝ} {a b T c : ℝ} (hc : 0 ≤ c) (hab : a ≤ b) (hbT : b < T)
    (hf : ∀ t ∈ Ioc a b, c / (T - t) ≤ f t) :
    ENNReal.ofReal (c * Real.log ((T - a) / (T - b))) ≤
      ∫⁻ t in Ioc a b, ENNReal.ofReal (f t) := by
  have hcont : ContinuousOn (fun t : ℝ => c * (T - t)⁻¹) (Icc a b) :=
    continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).inv₀
      (fun t ht => ne_of_gt (show 0 < T - t by linarith [ht.2])))
  have hint : IntervalIntegrable (fun t : ℝ => c * (T - t)⁻¹) volume a b :=
    hcont.intervalIntegrable_of_Icc hab
  have hn : 0 ≤ᵐ[volume.restrict (Ioc a b)] (fun t : ℝ => c * (T - t)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg hc (inv_nonneg.mpr (by linarith [ht.2]))
  have hlog : (∫ t in a..b, (T - t)⁻¹) = Real.log ((T - a) / (T - b)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) T]
    exact integral_inv_of_pos (sub_pos.mpr hbT) (sub_pos.mpr (hab.trans_lt hbT))
  have heq : (∫⁻ t in Ioc a b, ENNReal.ofReal (c * (T - t)⁻¹)) =
      ENNReal.ofReal (c * Real.log ((T - a) / (T - b))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint.1 hn,
      ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul, hlog]
  rw [← heq]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ENNReal.ofReal_le_ofReal (by simpa only [div_eq_mul_inv] using hf t ht)

theorem exists_logarithmic_integral_lower_bound {c : ℝ} (hc : 0 < c)
    (Lambda : ℝ) :
    ∃ theta : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧
      Lambda < c * Real.log ((1 - theta)⁻¹) := by
  let theta := 1 - Real.exp (-(|Lambda| / c + 1))
  have hp : 0 < |Lambda| / c + 1 := by positivity
  have he : Real.exp (-(|Lambda| / c + 1)) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hp)
  have ht0 : 0 < theta := by dsimp [theta]; linarith
  have ht1 : theta < 1 := by dsimp [theta]; linarith [Real.exp_pos (-(|Lambda| / c + 1))]
  have hlog : Real.log ((1 - theta)⁻¹) = |Lambda| / c + 1 := by
    dsimp [theta]
    rw [sub_sub_cancel, Real.log_inv, Real.log_exp]
    ring
  refine ⟨theta, ⟨ht0, ht1⟩, ?_⟩
  rw [hlog]
  have heq : c * (|Lambda| / c + 1) = |Lambda| + c := by field_simp
  rw [heq]
  linarith [le_abs_self Lambda]

end DifferentialGeometry.Analysis
