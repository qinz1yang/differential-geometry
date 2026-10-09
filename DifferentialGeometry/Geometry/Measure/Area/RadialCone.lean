/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.Calculus.Interpolation.RadialCone
import DifferentialGeometry.Geometry.Measure.Area.ChangeOfFrame
import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Area of the literal radial cone over a Lipschitz periodic loop

The estimates use the actual parameterized loop. No injectivity or nonzero-speed
condition is imposed, and the cone itself is not replaced by another filling.
-/

noncomputable section

open Set MeasureTheory Filter ContinuousLinearMap
open DifferentialGeometry.Topology
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

private theorem integral_Icc_comp_circle_parameter (g : ℝ → ℝ) :
    (∫ θ in Icc (-Real.pi) Real.pi, g θ) =
      (2 * Real.pi) * ∫ t in Icc (0 : ℝ) 1, g (2 * Real.pi * t - Real.pi) := by
  have h := intervalIntegral.smul_integral_comp_mul_sub (a := 0) (b := 1)
    g (2 * Real.pi) Real.pi
  have hπ : 2 * Real.pi * 1 - Real.pi = Real.pi := by ring
  simp only [mul_zero, zero_sub, hπ, smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at h
  exact h.symm

private theorem integral_unitDisk_eq_polar (f : ℂ → ℝ) :
    (∫ z in Metric.closedBall (0 : ℂ) 1, f z) =
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi, p.1 * f (Complex.polarCoord.symm p) := by
  let A := Metric.closedBall (0 : ℂ) 1
  let B : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)
  have hA : MeasurableSet A := measurableSet_closedBall
  have hB : MeasurableSet B := measurableSet_Icc.prod MeasurableSet.univ
  rw [← integral_indicator hA, ← Complex.integral_comp_polarCoord_symm]
  have heq : (∫ p in polarCoord.target, p.1 • A.indicator f (Complex.polarCoord.symm p)) =
      ∫ p in polarCoord.target, B.indicator
        (fun p => p.1 * f (Complex.polarCoord.symm p)) p := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    have hp0 : 0 < p.1 := hp.1
    have hmem : Complex.polarCoord.symm p ∈ A ↔ p ∈ B := by
      simp [A, B, abs_of_pos hp0, hp0.le]
    by_cases h : p ∈ B
    · simp only [indicator_of_mem (hmem.mpr h), indicator_of_mem h, smul_eq_mul]
    · simp only [indicator_of_notMem (mt hmem.mp h), indicator_of_notMem h, smul_zero]
  rw [heq, setIntegral_indicator hB]
  have hset : polarCoord.target ∩ B = Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [polarCoord_target, B, mem_inter_iff, mem_prod, mem_Ioi, mem_Icc,
      mem_univ, and_true, mem_Ioo, mem_Ioc]
    constructor
    · rintro ⟨⟨hp, hθ⟩, hρ⟩
      exact ⟨⟨hp, hρ.2⟩, hθ⟩
    · rintro ⟨hρ, hθ⟩
      exact ⟨⟨hρ.1, hθ⟩, hρ.1.le, hρ.2⟩
  rw [hset]
  exact setIntegral_congr_set (Measure.set_prod_ae_eq Ioc_ae_eq_Icc Ioo_ae_eq_Icc)

private theorem integral_unitDisk_eq_normalized_polar_of_bounded
    {f : ℂ → ℝ} (hf : Measurable f) {B : ℝ}
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖f z‖ ≤ B) :
    (∫ z in Metric.closedBall (0 : ℂ) 1, f z) =
      (2 * Real.pi) * ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        p.1 * f (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) := by
  have hi {s : Set ℝ} (hs : IsCompact s) (θ : ℝ × ℝ → ℝ) (hθ : Measurable θ) :
      IntegrableOn (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm (p.1, θ p)))
        (Icc (0 : ℝ) 1 ×ˢ s) := by
    have hp : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm (p.1, θ p)) := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    have hm := measurable_fst.mul (hf.comp hp)
    apply IntegrableOn.of_bound ((isCompact_Icc.prod hs).measure_lt_top)
      hm.aestronglyMeasurable (max B 0)
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod hs.measurableSet)] with p hp
    have hn : ‖Complex.polarCoord.symm (p.1, θ p)‖ ≤ 1 := by
      simpa only [Complex.norm_polarCoord_symm, abs_of_nonneg hp.1.1] using hp.1.2
    change ‖p.1 * f (Complex.polarCoord.symm (p.1, θ p))‖ ≤ max B 0
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hp.1.1]
    exact (mul_le_mul hp.1.2 (hbound _ (Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using hn))) (norm_nonneg _) zero_le_one).trans
        (by simp)
  rw [integral_unitDisk_eq_polar]
  have hraw := hi (s := Icc (-Real.pi) Real.pi) isCompact_Icc Prod.snd measurable_snd
  have hnorm := hi (s := Icc (0 : ℝ) 1) isCompact_Icc
    (fun p => 2 * Real.pi * p.2 - Real.pi) (by fun_prop)
  rw [Measure.volume_eq_prod] at ⊢ hraw hnorm
  rw [setIntegral_prod _ hraw, setIntegral_prod _ hnorm]
  simp_rw [integral_const_mul, integral_Icc_comp_circle_parameter]
  rw [← integral_const_mul]
  congr 1
  funext ρ
  ring

private theorem hasFDerivAt_complex_polar (p : ℝ × ℝ) :
    HasFDerivAt Complex.polarCoord.symm
      (Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm p)) p := by
  change HasFDerivAt (Complex.equivRealProdCLM.symm ∘ polarCoord.symm) _ p
  exact Complex.equivRealProdCLM.symm.hasFDerivAt.comp p (hasFDerivAt_polarCoord_symm p)

private theorem complex_polar_derivative_radial (p : ℝ × ℝ) :
    (fderiv ℝ Complex.polarCoord.symm p) (1, 0) =
      Real.cos p.2 • (1 : ℂ) + Real.sin p.2 • Complex.I := by
  rw [(hasFDerivAt_complex_polar p).fderiv]
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, Complex.real_smul]

private theorem complex_polar_derivative_angular (p : ℝ × ℝ) :
    (fderiv ℝ Complex.polarCoord.symm p) (0, 1) =
      p.1 • ((-Real.sin p.2) • (1 : ℂ) + Real.cos p.2 • Complex.I) := by
  rw [(hasFDerivAt_complex_polar p).fderiv]
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, Complex.real_smul]
  ring

private theorem hasFDerivAt_affine_angle (c d : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => (q.1, c * q.2 + d))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (c • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  simpa only [Pi.smul_apply, smul_eq_mul] using!
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk
      (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_smul c).add_const d)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem polar_fderiv_twoJacobian_le (g : ℂ → F) {p : ℝ × ℝ}
    (hp : 0 < p.1) :
    p.1 * euclideanAreaDensity g (Complex.polarCoord.symm p) ≤
      twoJacobian (fderiv ℝ (g ∘ Complex.polarCoord.symm) p (1, 0))
        (fderiv ℝ (g ∘ Complex.polarCoord.symm) p (0, 1)) := by
  by_cases hg : DifferentiableAt ℝ g (Complex.polarCoord.symm p)
  · let A := fderiv ℝ g (Complex.polarCoord.symm p)
    have hchain := fderiv_comp p hg (hasFDerivAt_complex_polar p).differentiableAt
    have hr : fderiv ℝ (g ∘ Complex.polarCoord.symm) p (1, 0) =
        Real.cos p.2 • A 1 + Real.sin p.2 • A Complex.I := by
      rw [hchain, ContinuousLinearMap.comp_apply, complex_polar_derivative_radial]
      change A _ = _
      simp only [map_add, map_smul]
    have ht : fderiv ℝ (g ∘ Complex.polarCoord.symm) p (0, 1) =
        p.1 • ((-Real.sin p.2) • A 1 + Real.cos p.2 • A Complex.I) := by
      rw [hchain, ContinuousLinearMap.comp_apply, complex_polar_derivative_angular]
      simp only [map_smul, map_add]
      rfl
    have hdet : Real.cos p.2 * Real.cos p.2 - Real.sin p.2 * (-Real.sin p.2) = 1 := by
      nlinarith [Real.cos_sq_add_sin_sq p.2]
    have hrot : twoJacobian (Real.cos p.2 • A 1 + Real.sin p.2 • A Complex.I)
        ((-Real.sin p.2) • A 1 + Real.cos p.2 • A Complex.I) =
          twoJacobian (A 1) (A Complex.I) := by
      rw [twoJacobian_changeOfFrame, hdet, abs_one, one_mul]
    rw [hr, ht]
    change p.1 * twoJacobian (A 1) (A Complex.I) ≤ _
    simpa only [one_smul, one_mul, abs_of_pos hp, hrot] using
      (twoJacobian_smul (Real.cos p.2 • A 1 + Real.sin p.2 • A Complex.I)
        ((-Real.sin p.2) • A 1 + Real.cos p.2 • A Complex.I) 1 p.1).ge
  · rw [euclideanAreaDensity_eq_zero_of_not_differentiableAt hg, mul_zero]
    exact twoJacobian_nonneg _ _

private theorem normalized_polar_fderiv_twoJacobian_le (g : ℂ → F)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    (2 * Real.pi) * p.1 * euclideanAreaDensity g
        (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) ≤
      twoJacobian
        (fderiv ℝ (fun q : ℝ × ℝ =>
          g (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) p (1, 0))
        (fderiv ℝ (fun q : ℝ × ℝ =>
          g (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) p (0, 1)) := by
  let A : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, 2 * Real.pi * q.2 - Real.pi)
  let H : ℝ × ℝ → F := g ∘ Complex.polarCoord.symm
  have hp' : 0 < (A p).1 := hp
  have h := polar_fderiv_twoJacobian_le g hp'
  by_cases hH : DifferentiableAt ℝ H (A p)
  · have hA : HasFDerivAt A
        ((fst ℝ ℝ ℝ).prod ((2 * Real.pi) • snd ℝ ℝ ℝ)) p := by
      simpa only [A, sub_eq_add_neg] using hasFDerivAt_affine_angle (2 * Real.pi) (-Real.pi) p
    have hchain := fderiv_comp p hH hA.differentiableAt
    have hr : fderiv ℝ (H ∘ A) p (1, 0) = fderiv ℝ H (A p) (1, 0) := by
      rw [hchain, hA.fderiv]
      simp
    have ht : fderiv ℝ (H ∘ A) p (0, 1) =
        (2 * Real.pi) • fderiv ℝ H (A p) (0, 1) := by
      rw [hchain, hA.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply,
        smul_eq_mul, mul_one]
      rw [show (0, 2 * Real.pi) = (2 * Real.pi) • ((0, 1) : ℝ × ℝ) by ext <;> simp,
        map_smul]
    change _ ≤ twoJacobian (fderiv ℝ (H ∘ A) p (1, 0))
      (fderiv ℝ (H ∘ A) p (0, 1))
    rw [hr, ht]
    have hj := twoJacobian_smul (fderiv ℝ H (A p) (1, 0))
      (fderiv ℝ H (A p) (0, 1)) 1 (2 * Real.pi)
    simp only [one_smul, one_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hj
    rw [hj]
    simpa only [A, mul_assoc] using
      mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * Real.pi)
  · change (A p).1 * euclideanAreaDensity g (Complex.polarCoord.symm (A p)) ≤
      twoJacobian (fderiv ℝ H (A p) (1, 0)) (fderiv ℝ H (A p) (0, 1)) at h
    rw [fderiv_zero_of_not_differentiableAt hH] at h
    simp only [zero_apply, twoJacobian_zero_left] at h
    have hz := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * Real.pi)
    have hz' : (2 * Real.pi) * p.1 * euclideanAreaDensity g
        (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) ≤ 0 := by
      simpa only [A, mul_zero, mul_assoc] using hz
    exact hz'.trans (twoJacobian_nonneg _ _)

variable [FiniteDimensional ℝ F]

private theorem integrable_norm_deriv_of_lipschitz {a : ℝ → F} {K : ℝ≥0}
    (hLip : LipschitzWith K a) :
    IntegrableOn (fun t => ‖deriv a t‖) (Icc (0 : ℝ) 1) := by
  borelize F
  apply Integrable.of_bound (measurable_deriv a).norm.aestronglyMeasurable (K : ℝ)
  exact Eventually.of_forall fun t => by
    simpa only [norm_norm] using
      (show ‖deriv a t‖ ≤ (K : ℝ) from norm_deriv_le_of_lipschitz hLip)

private theorem integrable_cone_firstMoment (p : F) {a : ℝ → F} {K : ℝ≥0}
    (hLip : LipschitzWith K a) :
    IntegrableOn (fun t => ‖a t - p‖ * ‖deriv a t‖) (Icc (0 : ℝ) 1) := by
  borelize F
  have hm : Measurable (fun t => ‖a t - p‖ * ‖deriv a t‖) :=
    (hLip.continuous.sub continuous_const).norm.measurable.mul (measurable_deriv a).norm
  apply Integrable.of_bound hm.aestronglyMeasurable (((K : ℝ) + ‖a 0 - p‖) * K)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have ht0 : dist t 0 ≤ 1 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht.1] using ht.2
  have htK : dist (a t) (a 0) ≤ K :=
    (hLip.dist_le_mul t 0).trans (by simpa using mul_le_mul_of_nonneg_left ht0 K.coe_nonneg)
  have hvdist : dist (a t) p ≤ (K : ℝ) + dist (a 0) p :=
    (dist_triangle (a t) (a 0) p).trans (_root_.add_le_add htK le_rfl)
  have hv : ‖a t - p‖ ≤ (K : ℝ) + ‖a 0 - p‖ := by
    simpa only [dist_eq_norm] using hvdist
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg (a t - p)) (norm_nonneg (deriv a t)))]
  exact mul_le_mul hv (norm_deriv_le_of_lipschitz hLip)
    (norm_nonneg _) (add_nonneg K.coe_nonneg (norm_nonneg _))

/-- The area of the literal cone is bounded by half the radial first moment of
the speed of its supplied periodic parametrization. -/
theorem euclideanArea_periodicLoopCone_le_firstMoment
    (p : F) {a : ℝ → F} {K : ℝ≥0}
    (ha : Function.Periodic a 1) (hLip : LipschitzWith K a) :
    euclideanArea (periodicLoopCone p ha) (Metric.closedBall (0 : ℂ) 1) ≤
      (1 / 2 : ℝ) * ∫ t in Icc (0 : ℝ) 1, ‖a t - p‖ * ‖deriv a t‖ := by
  borelize F
  let g := periodicLoopCone p ha
  let e := euclideanAreaDensity g
  let q (t : ℝ) := ‖a t - p‖ * ‖deriv a t‖
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  obtain ⟨C, hC⟩ := exists_lipschitzWith_periodicLoopCone p ha hLip
  have hemeas : Measurable e := measurable_euclideanAreaDensity g
  have heb (z : ℂ) : ‖e z‖ ≤ (C : ℝ) ^ 2 := by
    rw [Real.norm_of_nonneg (euclideanAreaDensity_nonneg g z)]
    exact euclideanAreaDensity_le hC z
  have hqi : Integrable q μ := integrable_cone_firstMoment p hLip
  have hradi : Integrable (fun t : ℝ => t) μ := continuous_id.integrableOn_Icc
  have hright : Integrable (fun z : ℝ × ℝ => z.1 * q z.2) (μ.prod μ) := hradi.mul_prod hqi
  let w (z : ℝ × ℝ) := z.1 * e
    (Complex.polarCoord.symm (z.1, 2 * Real.pi * z.2 - Real.pi))
  have hwmeas : Measurable w := by
    apply measurable_fst.mul
    apply hemeas.comp
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hw : Integrable w (μ.prod μ) := by
    apply Integrable.of_bound hwmeas.aestronglyMeasurable ((C : ℝ) ^ 2)
    have hx : ∀ᵐ z : ℝ × ℝ ∂μ.prod μ, z.1 ∈ Icc (0 : ℝ) 1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hx] with z hz
    dsimp only [w]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hz.1]
    exact (mul_le_mul hz.2 (heb _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hrad : ∀ᵐ z ∂μ.prod μ, 0 < z.1 := by
    apply Measure.quasiMeasurePreserving_fst.ae
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), 0 < t
    rw [← restrict_Ioc_eq_restrict_Icc]
    exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ht.1
  have had : ∀ᵐ z ∂μ.prod μ, DifferentiableAt ℝ a z.2 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae hLip.ae_differentiableAt_real)
  have hbound : ∀ᵐ z ∂μ.prod μ, (2 * Real.pi) * w z ≤ z.1 * q z.2 := by
    filter_upwards [hrad, had] with z hz hza
    have hp := normalized_polar_fderiv_twoJacobian_le g hz
    have hc := fderiv_periodicLoopCone_normalized_polar p ha hz hza
    rw [hc.1, hc.2] at hp
    have hj := twoJacobian_smul (a z.2 - p) (deriv a z.2) 1 z.1
    simp only [one_smul, one_mul, abs_of_pos hz] at hj
    rw [hj] at hp
    have hnorm := mul_le_mul_of_nonneg_left
      (twoJacobian_le_norm_mul (a z.2 - p) (deriv a z.2)) hz.le
    dsimp only [w, q, e]
    simpa only [mul_assoc] using hp.trans hnorm
  have hineq := integral_mono_ae (hw.const_mul (2 * Real.pi)) hright hbound
  rw [integral_const_mul] at hineq
  have heq := integral_unitDisk_eq_normalized_polar_of_bounded hemeas (fun z _ => heb z)
  change (∫ z in Metric.closedBall (0 : ℂ) 1, e z) ≤ _
  rw [heq, Measure.volume_eq_prod, ← Measure.prod_restrict]
  apply hineq.trans_eq
  rw [integral_prod _ hright]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]
  have hrint : (∫ t, t ∂μ) = 1 / 2 := by
    change (∫ t in Icc (0 : ℝ) 1, t) = 1 / 2
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      integral_id]
    norm_num
  rw [hrint]

/-- A radius bound gives area at most half the radius times the integral of the
speed, without changing the supplied parametrized loop or its cone. -/
theorem euclideanArea_periodicLoopCone_le_radius_mul_length
    (p : F) {a : ℝ → F} {K : ℝ≥0}
    (ha : Function.Periodic a 1) (hLip : LipschitzWith K a)
    {R : ℝ} (hbound : ∀ t, ‖a t - p‖ ≤ R) :
    euclideanArea (periodicLoopCone p ha) (Metric.closedBall (0 : ℂ) 1) ≤
      (R / 2) * ∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖ := by
  have hi := integral_mono_ae (integrable_cone_firstMoment p hLip)
    ((integrable_norm_deriv_of_lipschitz hLip).const_mul R)
    (Eventually.of_forall fun t => mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _))
  rw [integral_const_mul] at hi
  calc
    _ ≤ (1 / 2 : ℝ) * ∫ t in Icc (0 : ℝ) 1, ‖a t - p‖ * ‖deriv a t‖ :=
      euclideanArea_periodicLoopCone_le_firstMoment p ha hLip
    _ ≤ (1 / 2 : ℝ) * (R * ∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = _ := by ring

end DifferentialGeometry.Geometry
