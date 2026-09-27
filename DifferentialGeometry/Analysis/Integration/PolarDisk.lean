import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem integrableOn_polar_of_integrableOn_ball
    {F : ℂ → E} {R : ℝ} (hF : IntegrableOn F (Metric.ball (0 : ℂ) R)) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi) := by
  let f : ℂ → E := (Metric.ball (0 : ℂ) R).indicator F
  have hfi : Integrable f := (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr hF
  let G : ℝ × ℝ → E := f ∘ Complex.measurableEquivRealProd.symm
  have hG : Integrable G :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hfi
  have hpolar := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn G).mp hG.integrableOn
  have hsub : Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi ⊆ polarCoord.target := by
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  apply (hpolar.mono_set hsub).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  have hz : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) R := by
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
      abs_of_pos hp.1.1] using hp.1.2
  simp only [det_fderivPolarCoordSymm, abs_of_pos hp.1.1, G, Function.comp_apply,
    Complex.measurableEquivRealProd_symm_polarCoord_symm_apply, f, indicator_of_mem hz]

private theorem integral_ball_zero_eq_polar
    (F : ℂ → E) (R : ℝ) :
    (∫ z in Metric.ball (0 : ℂ) R, F z) =
      ∫ p in Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • F (Complex.polarCoord.symm p) := by
  let A := Metric.ball (0 : ℂ) R
  let B : Set (ℝ × ℝ) := Iio R ×ˢ (univ : Set ℝ)
  have hB : MeasurableSet B := measurableSet_Iio.prod MeasurableSet.univ
  rw [← integral_indicator Metric.isOpen_ball.measurableSet,
    ← Complex.integral_comp_polarCoord_symm]
  have heq : (∫ p in polarCoord.target, p.1 • A.indicator F (Complex.polarCoord.symm p)) =
      ∫ p in polarCoord.target, B.indicator
        (fun p => p.1 • F (Complex.polarCoord.symm p)) p := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    have hp0 : 0 < p.1 := hp.1
    have hm : Complex.polarCoord.symm p ∈ A ↔ p ∈ B := by
      simp only [A, B, Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
        abs_of_pos hp0, mem_prod, mem_Iio, mem_univ, and_true]
    by_cases h : p ∈ B
    · simp only [indicator_of_mem (hm.mpr h), indicator_of_mem h]
    · simp only [indicator_of_notMem (mt hm.mp h), indicator_of_notMem h, smul_zero]
  rw [heq, setIntegral_indicator hB]
  have hs : polarCoord.target ∩ B = Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [polarCoord_target, B, mem_inter_iff, mem_prod, mem_Ioi, mem_Iio,
      mem_univ, and_true, mem_Ioo]
    tauto
  rw [hs]

theorem integral_ball_zero_eq_integral_circle
    {F : ℂ → E} {R : ℝ} (hF : IntegrableOn F (Metric.ball (0 : ℂ) R)) :
    (∫ z in Metric.ball (0 : ℂ) R, F z) =
      ∫ r in Ioo (0 : ℝ) R, r • ∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ) := by
  have hi := integrableOn_polar_of_integrableOn_ball hF
  rw [integral_ball_zero_eq_polar F R, Measure.volume_eq_prod,
    setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using hi)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hp (θ : ℝ) : Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  simp_rw [hp]
  rw [integral_smul]

variable [CompleteSpace E]

theorem integral_unit_disk_eq_of_circle_integral
    {F : ℂ → E} (hF : IntegrableOn F (Metric.ball (0 : ℂ) 1))
    (n : ℕ) (c : E)
    (hcircle : ∀ r ∈ Ioo (0 : ℝ) 1,
      (∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ)) = r ^ n • c) :
    (∫ z in Metric.ball (0 : ℂ) 1, F z) = (1 / ((n : ℝ) + 2)) • c := by
  rw [integral_ball_zero_eq_integral_circle hF]
  have hradial : (∫ r in Ioo (0 : ℝ) 1, r • ∫ θ in Ioo (-Real.pi) Real.pi,
      F (circleMap 0 r θ)) = ∫ r in Ioo (0 : ℝ) 1, r ^ (n + 1) • c := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    change r • (∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ)) = r ^ (n + 1) • c
    rw [hcircle r hr, smul_smul, pow_succ']
  rw [hradial, integral_smul_const]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp [integral_pow, Nat.cast_add, Nat.cast_one]
  ring

theorem integral_unit_disk_eq_of_complex_circle_integral
    {F : ℂ → ℂ} (hF : IntegrableOn F (Metric.ball (0 : ℂ) 1))
    (n : ℕ) (c : ℂ)
    (hcircle : ∀ r ∈ Ioo (0 : ℝ) 1,
      (∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ)) = c * (r : ℂ) ^ n) :
    (∫ z in Metric.ball (0 : ℂ) 1, F z) = c / ((n : ℂ) + 2) := by
  have hc : ∀ r ∈ Ioo (0 : ℝ) 1,
      (∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ)) = r ^ n • c := by
    intro r hr
    rw [hcircle r hr, Complex.real_smul, Complex.ofReal_pow, mul_comm]
  rw [integral_unit_disk_eq_of_circle_integral hF n c hc, Complex.real_smul]
  push_cast
  ring

end DifferentialGeometry.Analysis

end
