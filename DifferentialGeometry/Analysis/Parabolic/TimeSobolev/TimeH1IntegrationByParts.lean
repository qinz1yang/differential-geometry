import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Energy

open MeasureTheory Set
open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  {T : ℝ}

theorem integration_by_parts (u v : timeH1 X T) (hT : 0 ≤ T) :
    inner ℝ (u.toFun T) (v.toFun T) - inner ℝ (u.toFun 0) (v.toFun 0) =
      inner ℝ u.toFunL2 v.deriv + inner ℝ v.toFunL2 u.deriv := by
  have hu := u.norm_sq_sub_norm_sq_eq_two_inner hT
  have hv := v.norm_sq_sub_norm_sq_eq_two_inner hT
  have huv := (u + v).norm_sq_sub_norm_sq_eq_two_inner hT
  have hadd : (u + v).toFunL2 = u.toFunL2 + v.toFunL2 :=
    (toTimeL2 X T).map_add u v
  rw [toFun_add u v ⟨hT, le_rfl⟩, toFun_add u v ⟨le_rfl, hT⟩,
    hadd, deriv_add] at huv
  simp only [norm_add_sq_real, inner_add_left, inner_add_right] at huv
  linarith

theorem integration_by_parts_integral (u v : timeH1 X T) (hT : 0 ≤ T) :
    inner ℝ (u.toFun T) (v.toFun T) - inner ℝ (u.toFun 0) (v.toFun 0) =
      (∫ t, inner ℝ (u.toFun t) (v.deriv t) ∂timeMeasure T) +
        ∫ t, inner ℝ (v.toFun t) (u.deriv t) ∂timeMeasure T := by
  rw [u.integration_by_parts v hT, TimeSobolev.inner_def, TimeSobolev.inner_def]
  have hu : (u.toFunL2 : ℝ → X) =ᵐ[timeMeasure T] u.toFun :=
    TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun
  have hv : (v.toFunL2 : ℝ → X) =ᵐ[timeMeasure T] v.toFun :=
    TimeSobolev.coeFn_ofContinuousOn v.continuousOn_toFun
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply integral_congr_ae
    filter_upwards [hu] with t ht
    rw [ht]
  · apply integral_congr_ae
    filter_upwards [hv] with t ht
    rw [ht]

theorem integral_mul_deriv_add_deriv_mul
    (u : timeH1 ℝ T) (hT : 0 ≤ T) {η : ℝ → ℝ}
    (hη : ContDiffOn ℝ 1 η (Icc (0 : ℝ) T)) :
    u.toFun T * η T - u.toFun 0 * η 0 =
      (∫ t, u.toFun t * _root_.deriv η t ∂timeMeasure T) +
        ∫ t, η t * u.deriv t ∂timeMeasure T := by
  let v := ofContDiffOn hT η hη
  have hv : EqOn v.toFun η (Icc (0 : ℝ) T) := toFun_ofContDiffOn hT η hη
  have h := u.integration_by_parts_integral v hT
  rw [hv ⟨hT, le_rfl⟩, hv ⟨le_rfl, hT⟩] at h
  simp only [Real.inner_apply] at h
  rw [h]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply integral_congr_ae
    filter_upwards [deriv_ofContDiffOn hT η hη] with t ht
    rw [ht]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hv ht]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1
