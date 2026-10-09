import DifferentialGeometry.Analysis.Complex.CauchyTransform.BoundedFixedPoint
import DifferentialGeometry.Analysis.Complex.CauchyTransform.BoundedWeakEquation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
noncomputable section

open Set Filter Metric MeasureTheory DifferentialGeometry.Analysis
open scoped Topology ContDiff

namespace DiskRegularity.ConsumerAudit

private theorem integrable_and_integral_realTestDbar_eq_zero
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : ℂ =>
      ((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) ∧
    (∫ z : ℂ,
      ((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) = 0 := by
  have hi (v : ℂ) : Integrable (fun z : ℂ => fderiv ℝ φ z v) :=
    ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have hz (v : ℂ) : (∫ z : ℂ, fderiv ℝ φ z v) = 0 := by
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := fun _ : ℂ => (1 : ℝ)) (g := φ) (v := v)
      (by simp)
      (by simpa using hi v)
      (by simpa using hφ.continuous.integrable_of_hasCompactSupport hc)
      (fun _ _ => differentiableAt_const _)
      (fun z _ => (hφ.differentiable one_ne_zero) z)
    simpa using hh
  have hi1 : Integrable (fun z : ℂ => (fderiv ℝ φ z (1 : ℂ) : ℂ)) := (hi 1).ofReal
  have hiI : Integrable (fun z : ℂ => (fderiv ℝ φ z Complex.I : ℂ)) := (hi Complex.I).ofReal
  refine ⟨(hi1.add (hiI.const_mul Complex.I)).div_const 2, ?_⟩
  rw [integral_div, integral_add hi1 (hiI.const_mul Complex.I), integral_const_mul]
  simp only [integral_complex_ofReal, hz, Complex.ofReal_zero, mul_zero, add_zero, zero_div]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- The gauge is selected once from the same bounded measurable coefficient. Its literal
ambient representative agrees at every disk point and satisfies the weak equation there. -/
theorem bounded_measurable_unit_gauge_with_weak_equation
    (a : ℂ) (R : ℝ) (hR : 0 < R)
    (A : closedBall a R → V →L[ℂ] V)
    (hA : AEStronglyMeasurable A (volume.comap ((↑) : closedBall a R → ℂ)))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
      ‖A w‖ ≤ B)
    (hk : 4 * R * B < 1 / 2) :
    ∃ P : C(closedBall a R, V →L[ℂ] V),
      P = 1 + CauchyTransform.boundedCoefficientCauchyTransform hR A hA hB hbound P ∧
      ‖P - 1‖ ≤ (4 * R * B) / (1 - 4 * R * B) ∧
      (∀ z : closedBall a R, IsUnit (P z)) ∧
      (let P₀ : ℂ → V →L[ℂ] V := fun z =>
        1 + diskCauchyIntegral (fun w => A w * P w) z
       (∀ z : closedBall a R, P₀ z = P z) ∧
       (∀ z ∈ closedBall a R, IsUnit (P₀ z)) ∧
       ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
         tsupport φ ⊆ ball a R →
         Integrable (fun z : ℂ =>
           (((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
             P₀ z) ∧
         (∫ z : ℂ,
           (((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
             P₀ z) =
           -(∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • (A w * P w)
             ∂(volume.comap ((↑) : closedBall a R → ℂ)))) := by
  obtain ⟨P, hP, hnear, hunit, hintegral⟩ :=
    CauchyTransform.exists_unit_bounded_integral_fixedPoint a R hR A hA B hB hbound hk
  refine ⟨P, hP, hnear, hunit, ?_⟩
  dsimp only
  refine ⟨fun z => (hintegral z).symm, ?_, ?_⟩
  · intro z hz
    exact (congrArg (fun T : V →L[ℂ] V => IsUnit T)
      (hintegral ⟨z, hz⟩)).mp (hunit ⟨z, hz⟩)
  · intro φ hφ hc hs
    have hprod : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)),
        ‖A w * P w‖ ≤ B * ‖P‖ := by
      filter_upwards [hbound] with w hw
      exact (norm_mul_le _ _).trans
        (mul_le_mul hw (P.norm_coe_le_norm w) (norm_nonneg _) hB)
    obtain ⟨hCi, hC⟩ := integrable_and_weak_equation_diskCauchyIntegral
      (fun w => A w * P w)
      (hA.mul P.continuous.stronglyMeasurable.aestronglyMeasurable) hprod hφ hc hs
    obtain ⟨hDi, hDzero⟩ := integrable_and_integral_realTestDbar_eq_zero hφ hc
    let D (z : ℂ) : ℂ :=
      ((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2
    have hconst : Integrable (fun z : ℂ => D z • (1 : V →L[ℂ] V)) := hDi.smul_const 1
    constructor
    · apply (hconst.add hCi).congr
      exact Eventually.of_forall fun z =>
        (smul_add (D z) 1 (diskCauchyIntegral (fun w => A w * P w) z)).symm
    · change (∫ z : ℂ, D z • (1 + diskCauchyIntegral (fun w => A w * P w) z)) = _
      simp_rw [smul_add]
      rw [integral_add hconst hCi, integral_smul_const, hDzero, zero_smul, zero_add]
      exact hC

end DiskRegularity.ConsumerAudit
