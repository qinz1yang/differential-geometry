import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Integral.Measure

theorem lintegral_exp_neg_Ioi (a : ℝ) :
    (∫⁻ r : ℝ in Ioi a, ENNReal.ofReal (Real.exp (-r))) =
      ENNReal.ofReal (Real.exp (-a)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi a)
    (Filter.Eventually.of_forall (fun r => (Real.exp_pos (-r)).le)),
    integral_exp_neg_Ioi]

theorem lintegral_exp_neg_mul_Ioi {c : ℝ} (hc : 0 < c) (a : ℝ) :
    (∫⁻ r : ℝ in Ioi a, ENNReal.ofReal (Real.exp (-c * r))) =
      ENNReal.ofReal (Real.exp (-c * a) / c) := by
  have hn : -c < 0 := neg_neg_of_pos hc
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi hn a)
    (Filter.Eventually.of_forall (fun r => (Real.exp_pos (-c * r)).le)),
    integral_exp_mul_Ioi hn]
  simp

theorem lintegral_exp_neg_halfLine_tail {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ r : ℝ in Ioi a, ENNReal.ofReal (Real.exp (-r))
      ∂((volume : Measure ℝ).restrict (Ici 0))) =
      ENNReal.ofReal (Real.exp (-a)) := by
  rw [Measure.restrict_restrict_of_subset (show Ioi a ⊆ Ici (0 : ℝ) from fun _ hr => ha.trans hr.le)]
  exact lintegral_exp_neg_Ioi a

theorem lintegral_exp_neg_halfLine_closed_tail {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ r : ℝ in Ici a, ENNReal.ofReal (Real.exp (-r))
      ∂((volume : Measure ℝ).restrict (Ici 0))) =
      ENNReal.ofReal (Real.exp (-a)) := by
  rw [← restrict_Ioi_eq_restrict_Ici
    (μ := (volume : Measure ℝ).restrict (Ici 0)) (a := a)]
  exact lintegral_exp_neg_halfLine_tail ha

end DifferentialGeometry.Integral.Measure
