import DifferentialGeometry.Analysis.Complex.CauchyTransform.FundamentalSolution
import DifferentialGeometry.Analysis.Complex.CauchyTransform.Disk
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory DifferentialGeometry.Analysis
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The ambient function uses exactly the defining disk integral and its
explicit subtype comap measure, for every ambient evaluation point. -/
def ambientCauchyIntegral {a : ℂ} {R : ℝ} (f : C(closedBall a R, F)) (z : ℂ) : F :=
  (Real.pi : ℂ)⁻¹ • ∫ w : closedBall a R, (z - (w : ℂ))⁻¹ • f w
    ∂(volume.comap ((↑) : closedBall a R → ℂ))

omit [CompleteSpace F] in
theorem ambientCauchyIntegral_eq_diskCauchyTransform {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : C(closedBall a R, F)) (z : closedBall a R) :
    ambientCauchyIntegral f z = diskCauchyTransform a R hR f z :=
  (diskCauchyTransform_apply a R hR f z).symm

private def testDbar (φ : ℂ → ℝ) (z : ℂ) : ℂ :=
  ((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2

private theorem continuous_testDbar {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (testDbar φ) := by
  have hd := hφ.continuous_fderiv (by norm_num)
  exact ((Complex.continuous_ofReal.comp (hd.clm_apply continuous_const)).add
    (continuous_const.mul
      (Complex.continuous_ofReal.comp (hd.clm_apply continuous_const)))).div_const 2

private theorem compactSupport_testDbar {φ : ℂ → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (testDbar φ) := by
  apply HasCompactSupport.intro hc.isCompact
  intro z hz
  simp only [testDbar, fderiv_of_notMem_tsupport ℝ hz, _root_.zero_apply,
    Complex.ofReal_zero, mul_zero, add_zero, zero_div]

private theorem testDbar_eq_zero_outside_disk {a : ℂ} {R : ℝ} {φ : ℂ → ℝ}
    (hs : tsupport φ ⊆ ball a R) {z : ℂ} (hz : z ∉ closedBall a R) :
    testDbar φ z = 0 := by
  have hn : z ∉ tsupport φ := fun hm => hz (ball_subset_closedBall (hs hm))
  simp only [testDbar, fderiv_of_notMem_tsupport ℝ hn, _root_.zero_apply,
    Complex.ofReal_zero, mul_zero, add_zero, zero_div]

private theorem translated_kernel_norm_bound {a : ℂ} {R : ℝ} (w : closedBall a R) :
    (∫ z in closedBall a R, ‖((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹‖) ≤
      ∫ z in closedBall (0 : ℂ) (2 * R), ‖((Real.pi : ℂ) * z)⁻¹‖ := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.addRight (-(w : ℂ))
  have hm : MeasurePreserving e volume volume :=
    measurePreserving_add_right volume (-(w : ℂ))
  have hpre : e ⁻¹' closedBall (0 : ℂ) (2 * R) = closedBall (w : ℂ) (2 * R) := by
    ext z
    simp only [mem_preimage, mem_closedBall, dist_eq_norm,
      e, Homeomorph.coe_addRight, sub_eq_add_neg, neg_zero, add_zero]
  have hi : IntegrableOn (fun z : ℂ => ‖((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹‖)
      (closedBall (w : ℂ) (2 * R)) :=
    (locallyIntegrable_cauchyKernel (w : ℂ)).integrableOn_isCompact
      (isCompact_closedBall _ _) |>.norm
  have hsub : closedBall a R ⊆ closedBall (w : ℂ) (2 * R) := by
    intro z hz
    apply (dist_triangle z a w).trans
    have hw : dist a (w : ℂ) ≤ R := by
      simpa only [mem_closedBall, dist_comm] using w.property
    linarith [show dist z a ≤ R from hz]
  calc
    _ ≤ ∫ z in closedBall (w : ℂ) (2 * R), ‖((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹‖ :=
      setIntegral_mono_set hi (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hsub)
    _ = _ := by
      have h := hm.setIntegral_preimage_emb e.measurableEmbedding
        (fun z : ℂ => ‖((Real.pi : ℂ) * z)⁻¹‖) (closedBall (0 : ℂ) (2 * R))
      change (∫ z in e ⁻¹' closedBall (0 : ℂ) (2 * R),
        ‖((Real.pi : ℂ) * e z)⁻¹‖) = _ at h
      rw [hpre] at h
      simpa only [e, Homeomorph.coe_addRight, sub_eq_add_neg] using h

omit [CompleteSpace F] in
private theorem integrable_joint_test_kernel {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ ball a R) :
    Integrable (fun q : closedBall a R × ℂ =>
      (testDbar φ q.2 * ((Real.pi : ℂ) * (q.2 - (q.1 : ℂ)))⁻¹) • f q.1)
      ((volume.comap ((↑) : closedBall a R → ℂ)).prod volume) := by
  let μ : Measure (closedBall a R) := volume.comap ((↑) : closedBall a R → ℂ)
  have : IsFiniteMeasureOnCompacts μ :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe isClosed_closedBall.measurableSet)
  let J (w : closedBall a R) (z : ℂ) :=
    (testDbar φ z * ((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹) • f w
  have hD := continuous_testDbar hφ
  have hcD := compactSupport_testDbar hc
  obtain ⟨C, hC, hbound⟩ := (hcD.isCompact_range hD).isBounded.exists_pos_norm_lt
  have hDnorm (z : ℂ) : ‖testDbar φ z‖ ≤ C := (hbound _ ⟨z, rfl⟩).le
  let B : ℝ := ∫ z in closedBall (0 : ℂ) (2 * R), ‖((Real.pi : ℂ) * z)⁻¹‖
  have hmeas : AEStronglyMeasurable (Function.uncurry J) (μ.prod volume) := by
    have hk : Measurable (fun q : closedBall a R × ℂ =>
        ((Real.pi : ℂ) * (q.2 - (q.1 : ℂ)))⁻¹) :=
      (measurable_const.mul
        (measurable_snd.sub (measurable_subtype_coe.comp measurable_fst))).inv
    exact ((hD.comp continuous_snd).aestronglyMeasurable.mul
      hk.aestronglyMeasurable).smul (f.continuous.comp continuous_fst).aestronglyMeasurable
  have hfiber (w : closedBall a R) : Integrable (J w) := by
    have hi := (integrable_and_integral_cauchyKernel_mul_realTestDbar hφ hc (w : ℂ)).1
    have hscalar : Integrable (fun z : ℂ =>
        testDbar φ z * ((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹) := by
      simpa only [testDbar, mul_comm] using hi
    exact hscalar.smul_const (f w)
  have hfiberBound (w : closedBall a R) : (∫ z : ℂ, ‖J w z‖) ≤ C * ‖f‖ * B := by
    let major (z : ℂ) := (closedBall a R).indicator
      (fun z => (C * ‖f‖) * ‖((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹‖) z
    have him : Integrable major := by
      apply (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      exact (((locallyIntegrable_cauchyKernel (w : ℂ)).integrableOn_isCompact
        (isCompact_closedBall a R)).norm).const_mul (C * ‖f‖)
    have hpoint (z : ℂ) : ‖J w z‖ ≤ major z := by
      by_cases hz : z ∈ closedBall a R
      · rw [show major z = (C * ‖f‖) * ‖((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹‖ from
          indicator_of_mem hz _]
        dsimp only [J]
        rw [norm_smul, norm_mul]
        calc
          _ ≤ (C * ‖((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹‖) * ‖f‖ :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hDnorm z) (norm_nonneg _))
              (f.norm_coe_le_norm w) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      · simp only [J, testDbar_eq_zero_outside_disk hs hz, zero_mul, zero_smul,
          norm_zero, major, indicator_of_notMem hz, le_refl]
    calc
      _ ≤ ∫ z : ℂ, major z := integral_mono_ae (hfiber w).norm him
        (Eventually.of_forall hpoint)
      _ = (C * ‖f‖) * ∫ z in closedBall a R, ‖((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹‖ := by
        rw [show major = (closedBall a R).indicator
          (fun z => (C * ‖f‖) * ‖((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹‖) from rfl,
          integral_indicator isClosed_closedBall.measurableSet, integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (translated_kernel_norm_bound w) (by positivity)
  apply (integrable_prod_iff hmeas).mpr
  refine ⟨Eventually.of_forall hfiber, ?_⟩
  apply (integrable_const (C * ‖f‖ * B)).mono'
    hmeas.norm.integral_prod_right'
  exact Eventually.of_forall fun w => by
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hfiberBound w

/-- The same ambient Cauchy integral has the actual weak `∂bar` equation.
The joint Bochner integrability needed by Fubini is derived from the singular
kernel and the genuine compact test support, not supplied as a premise. -/
theorem integrable_and_weak_equation_ambientCauchyIntegral
    {a : ℂ} {R : ℝ} (f : C(closedBall a R, F))
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ ball a R) :
    Integrable (fun z : ℂ =>
      (((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
        ambientCauchyIntegral f z) ∧
    (∫ z : ℂ,
      (((fderiv ℝ φ z (1 : ℂ) : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
        ambientCauchyIntegral f z) =
      -(∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • f w
        ∂(volume.comap ((↑) : closedBall a R → ℂ))) := by
  let μ : Measure (closedBall a R) := volume.comap ((↑) : closedBall a R → ℂ)
  have : IsFiniteMeasureOnCompacts μ :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe isClosed_closedBall.measurableSet)
  let J (w : closedBall a R) (z : ℂ) :=
    (testDbar φ z * ((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹) • f w
  have hj : Integrable (Function.uncurry J) (μ.prod volume) :=
    integrable_joint_test_kernel f hφ hc hs
  have hinner (z : ℂ) : (∫ w : closedBall a R, J w z ∂μ) =
      testDbar φ z • ambientCauchyIntegral f z := by
    calc
      _ = ∫ w : closedBall a R,
          testDbar φ z • ((Real.pi : ℂ)⁻¹ • ((z - (w : ℂ))⁻¹ • f w)) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun w => by
          simp only [J, mul_inv_rev, smul_smul]
          congr 1
          ring
      _ = _ := by rw [integral_smul, integral_smul]; rfl
  have houter (w : closedBall a R) : (∫ z : ℂ, J w z) = -(φ (w : ℂ) : ℂ) • f w := by
    have h := (integrable_and_integral_cauchyKernel_mul_realTestDbar hφ hc (w : ℂ)).2
    calc
      _ = (∫ z : ℂ, ((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹ * testDbar φ z) • f w := by
        simp only [J, mul_comm (testDbar φ _), integral_smul_const]
      _ = _ := by rw [show (∫ z : ℂ, ((Real.pi : ℂ) * (z - (w : ℂ)))⁻¹ * testDbar φ z) =
        -(φ (w : ℂ) : ℂ) from h]
  refine ⟨hj.integral_prod_right.congr (Eventually.of_forall hinner), ?_⟩
  change (∫ z : ℂ, testDbar φ z • ambientCauchyIntegral f z) = _
  calc
    _ = ∫ z : ℂ, ∫ w : closedBall a R, J w z ∂μ :=
      integral_congr_ae (Eventually.of_forall fun z => (hinner z).symm)
    _ = ∫ w : closedBall a R, (∫ z : ℂ, J w z) ∂μ := (integral_integral_swap hj).symm
    _ = ∫ w : closedBall a R, -(φ (w : ℂ) : ℂ) • f w ∂μ :=
      integral_congr_ae (Eventually.of_forall houter)
    _ = _ := by simp only [neg_smul, integral_neg, μ]

/-- The scalar Cauchy kernel times a compactly supported test derivative is
jointly Bochner integrable for the actual disk comap and planar volume measures. -/
theorem integrable_joint_cauchyKernel_mul_realTestDbar {a : ℂ} {R : ℝ}
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ ball a R) :
    Integrable (fun q : closedBall a R × ℂ =>
      (((fderiv ℝ φ q.2 (1 : ℂ) : ℂ) +
        Complex.I * (fderiv ℝ φ q.2 Complex.I : ℂ)) / 2) *
        ((Real.pi : ℂ) * (q.2 - (q.1 : ℂ)))⁻¹)
      ((volume.comap ((↑) : closedBall a R → ℂ)).prod volume) := by
  simpa only [testDbar, ContinuousMap.const_apply, smul_eq_mul, mul_one] using
    (integrable_joint_test_kernel (ContinuousMap.const (closedBall a R) (1 : ℂ)) hφ hc hs)

end DifferentialGeometry.Analysis
