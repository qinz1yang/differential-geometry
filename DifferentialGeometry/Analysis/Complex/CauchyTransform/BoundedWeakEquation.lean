import DifferentialGeometry.Analysis.Complex.CauchyTransform.BoundedData
import DifferentialGeometry.Analysis.Complex.CauchyTransform.WeakEquation

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The literal Cauchy integral of bounded almost-everywhere strongly measurable disk data
satisfies the weak `∂bar` equation for every real compactly supported test in the open disk.
Both sides use the original disk comap measure; joint integrability follows from the
accepted scalar kernel estimate and the almost-everywhere bound on the actual data. -/
theorem integrable_and_weak_equation_diskCauchyIntegral
    {a : ℂ} {R : ℝ} (f : closedBall a R → F)
    (hf : AEStronglyMeasurable f (volume.comap ((↑) : closedBall a R → ℂ)))
    {B : ℝ}
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)), ‖f w‖ ≤ B)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ ball a R) :
    Integrable (fun z : ℂ =>
      (((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
        diskCauchyIntegral f z) ∧
    (∫ z : ℂ,
      (((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
        diskCauchyIntegral f z) =
      -(∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • f w
        ∂(volume.comap ((↑) : closedBall a R → ℂ))) := by
  let μ : Measure (closedBall a R) := volume.comap ((↑) : closedBall a R → ℂ)
  have : IsFiniteMeasureOnCompacts μ :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe isClosed_closedBall.measurableSet)
  let D (z : ℂ) : ℂ :=
    ((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2
  let J (w : closedBall a R) (z : ℂ) : F :=
    (D z * ((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹) • f w
  have hscalar : Integrable (fun q : closedBall a R × ℂ =>
      D q.2 * ((Real.pi : ℂ) * (q.2 - (q.1 : ℂ)))⁻¹) (μ.prod volume) :=
    integrable_joint_cauchyKernel_mul_realTestDbar hφ hc hs
  have hj : Integrable (Function.uncurry J) (μ.prod volume) := by
    apply (hscalar.norm.mul_const B).mono'
      (hscalar.aestronglyMeasurable.smul hf.comp_fst)
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ)
      (ν := (volume : Measure ℂ))).ae hbound] with q hq
    simp only [Pi.smul_apply', norm_smul]
    exact mul_le_mul_of_nonneg_left hq (norm_nonneg _)
  have hinner (z : ℂ) : (∫ w : closedBall a R, J w z ∂μ) =
      D z • diskCauchyIntegral f z := by
    calc
      _ = ∫ w : closedBall a R,
          D z • ((Real.pi : ℂ)⁻¹ • ((z - (w : ℂ))⁻¹ • f w)) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun w => by
          simp only [J, mul_inv_rev, smul_smul]
          congr 1
          ring
      _ = _ := by rw [integral_smul, integral_smul]; rfl
  have houter (w : closedBall a R) : (∫ z : ℂ, J w z) = -(φ (w : ℂ) : ℂ) • f w := by
    have h := (integrable_and_integral_cauchyKernel_mul_realTestDbar hφ hc (w : ℂ)).2
    calc
      _ = (∫ z : ℂ, ((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹ * D z) • f w := by
        simp only [J, mul_comm (D _), integral_smul_const]
      _ = _ := by rw [show (∫ z : ℂ, ((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹ * D z) =
        -(φ (w : ℂ) : ℂ) from h]
  refine ⟨hj.integral_prod_right.congr (Eventually.of_forall hinner), ?_⟩
  change (∫ z : ℂ, D z • diskCauchyIntegral f z) = _
  calc
    _ = ∫ z : ℂ, ∫ w : closedBall a R, J w z ∂μ :=
      integral_congr_ae (Eventually.of_forall fun z => (hinner z).symm)
    _ = ∫ w : closedBall a R, (∫ z : ℂ, J w z) ∂μ := (integral_integral_swap hj).symm
    _ = ∫ w : closedBall a R, -(φ (w : ℂ) : ℂ) • f w ∂μ :=
      integral_congr_ae (Eventually.of_forall houter)
    _ = _ := by simp only [neg_smul, integral_neg, μ]

end DifferentialGeometry.Analysis
