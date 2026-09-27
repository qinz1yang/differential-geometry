import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.ContDiff.Operations








noncomputable section

open Set MeasureTheory Filter
open scoped Topology Convolution ContDiff

namespace DifferentialGeometry.Analysis



theorem abs_log_le_self_add_inv {r : ℝ} (hr : 0 ≤ r) : |Real.log r| ≤ r + r⁻¹ := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have h₁ := Real.log_le_sub_one_of_pos hr
  have h₂ := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
  rw [Real.log_inv] at h₂
  apply abs_le.mpr
  constructor <;> linarith [inv_pos.mpr hr]




theorem locallyIntegrable_log_norm_complex :
    LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) volume := by
  have hinv : LocallyIntegrable (fun z : ℂ => ‖z‖⁻¹) volume := by
    apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
      (by simp [Complex.finrank_real_complex]) (by norm_num [Complex.finrank_real_complex])
    · exact Eventually.of_forall fun z => by simp [Real.rpow_neg_one]
    · fun_prop
  have hnorm : LocallyIntegrable (fun z : ℂ => ‖z‖) volume := continuous_norm.locallyIntegrable
  rw [locallyIntegrable_iff] at hinv hnorm ⊢
  intro K hK
  apply ((hnorm K hK).add (hinv K hK)).mono'
  · exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      change |Real.log ‖z‖| ≤ ‖z‖ + ‖z‖⁻¹
      exact abs_log_le_self_add_inv (norm_nonneg z)



def logarithmicPotential (κ : ℂ → ℝ) (z : ℂ) : ℝ :=
  -(1 / (2 * Real.pi)) * ∫ w : ℂ, κ w * Real.log ‖z - w‖




theorem contDiff_logarithmicPotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ (logarithmicPotential κ) := by
  have h := hc.contDiff_convolution_left (μ := (volume : Measure ℂ))
    (ContinuousLinearMap.mul ℝ ℝ) hκ
    locallyIntegrable_log_norm_complex
  exact contDiff_const.mul h

end DifferentialGeometry.Analysis
