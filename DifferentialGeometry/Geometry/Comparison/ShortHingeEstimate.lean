import DifferentialGeometry.Geometry.Comparison.HingeModel
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicSlope

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Real

noncomputable def shortHingeScale (a₀ θ : ℝ) : ℝ :=
  min 1 (min (a₀ / 2) ((sin θ / 2) * tanh a₀))

theorem shortHingeScale_pos {a₀ θ : ℝ} (ha₀ : 0 < a₀)
    (hθ : 0 < θ) (hθhalf : θ < Real.pi / 2) : 0 < shortHingeScale a₀ θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ (by linarith [pi_pos])
  have ht : 0 < tanh a₀ := by rw [tanh_eq_sinh_div_cosh]; exact div_pos (sinh_pos_iff.mpr ha₀) (cosh_pos _)
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

private theorem tanh_le_of_le {a b : ℝ} (hab : a ≤ b) : tanh a ≤ tanh b := by
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh,
    div_le_div_iff₀ (cosh_pos a) (cosh_pos b)]
  have h := sinh_nonneg_iff.mpr (sub_nonneg.mpr hab)
  rw [sinh_sub] at h
  nlinarith

theorem modelSide_short_hinge_le {a₀ a ℓ θ α : ℝ}
    (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (hℓ : 0 < ℓ)
    (hθ : 0 < θ) (hθhalf : θ < Real.pi / 2)
    (hα : 0 ≤ α) (hαθ : α ≤ Real.pi / 2 - θ)
    (hshort : ℓ ≤ shortHingeScale a₀ θ) :
    modelSideNegCurvature 1 a ℓ α ≤ a - (sin θ / 2) * ℓ := by
  have hsin : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ (by linarith [pi_pos])
  have hsinone := sin_le_one θ
  have hℓone : ℓ ≤ 1 := hshort.trans (min_le_left _ _)
  have hℓa : ℓ ≤ a₀ / 2 := hshort.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hℓtanh : ℓ ≤ (sin θ / 2) * tanh a :=
    (hshort.trans ((min_le_right _ _).trans (min_le_right _ _))).trans
      (mul_le_mul_of_nonneg_left (tanh_le_of_le ha) (by positivity))
  have hcos : sin θ ≤ cos α := by
    rw [← cos_pi_div_two_sub]
    exact cos_le_cos_of_nonneg_of_le_pi hα (by linarith [pi_pos]) hαθ
  have ha' : 0 < a := ha₀.trans_le ha
  have htarget : 0 ≤ a - (sin θ / 2) * ℓ := by
    have hh := mul_le_mul_of_nonneg_right hsinone hℓ.le
    nlinarith
  have hlinear : ℓ * cosh a ≤ (sin θ / 2) * sinh a := by
    rw [tanh_eq_sinh_div_cosh, ← mul_div_assoc] at hℓtanh
    exact (le_div_iff₀ (cosh_pos a)).mp hℓtanh
  have hquadratic : cosh a * ℓ ^ 2 ≤ (sin θ / 2) * sinh a * ℓ := by
    nlinarith [mul_le_mul_of_nonneg_right hlinear hℓ.le]
  have hcosh := cosh_sub_one_le_sq hℓ.le hℓone
  have hsinh := self_le_sinh_iff.mpr hℓ.le
  have hbound : cosh (modelSideNegCurvature 1 a ℓ α) ≤
      cosh a - (sin θ / 2) * sinh a * ℓ := by
    have hlaw := cosh_sqrt_mul_modelSideNegCurvature (κ := 1) (by norm_num) ha'.le hℓ.le (θ := α)
    norm_num only [sqrt_one, one_mul] at hlaw
    have h₁ := mul_le_mul_of_nonneg_left hcos (mul_nonneg
      (sinh_nonneg_iff.mpr ha'.le) (sinh_nonneg_iff.mpr hℓ.le))
    have h₂ := mul_le_mul_of_nonneg_left hcosh (cosh_pos a).le
    have h₃ := mul_le_mul_of_nonneg_left hsinh (mul_nonneg hsin.le (sinh_nonneg_iff.mpr ha'.le))
    nlinarith
  have hslope := cosh_sub_le_sinh_mul_sub htarget
    (sub_le_self a (mul_nonneg (by positivity) hℓ.le)) le_rfl
  have hh : cosh (modelSideNegCurvature 1 a ℓ α) ≤ cosh (a - (sin θ / 2) * ℓ) := by
    nlinarith
  have hle := cosh_le_cosh.mp hh
  rwa [abs_of_nonneg (modelSideNegCurvature_nonneg ha'.le hℓ.le), abs_of_nonneg htarget] at hle

end DifferentialGeometry.Geometry.Comparison.Toponogov

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p q : X}

theorem distance_drop_of_short_hinge (H : MinimizingHinge p q) {a₀ θ : ℝ}
    (ha₀ : 0 < a₀) (ha : a₀ ≤ dist H.center p) (hℓ : 0 < dist H.center q)
    (hθ : 0 < θ) (hθhalf : θ < Real.pi / 2)
    (hangle : H.germAngle 1 ≤ Real.pi / 2 - θ)
    (hcomparison : dist p q ≤ H.modelSide 1)
    (hshort : dist H.center q ≤ shortHingeScale a₀ θ) :
    (Real.sin θ / 2) * dist H.center q ≤ dist H.center p - dist p q := by
  have h := modelSide_short_hinge_le ha₀ ha hℓ hθ hθhalf
    (H.germAngle_mem_Icc 1).1 hangle hshort
  change H.modelSide 1 ≤ _ at h
  linarith

end Metric.MinimizingHinge
