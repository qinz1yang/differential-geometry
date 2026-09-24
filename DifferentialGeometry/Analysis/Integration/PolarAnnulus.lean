import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import DifferentialGeometry.Analysis.Integration.Measure.Polar.Complex
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.CircleIntegral

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace DifferentialGeometry.Analysis



theorem integral_annulus_eq_polar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {r R : ℝ} (hr : 0 < r) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f z) =
      ∫ p in Icc (r, -Real.pi) (R, Real.pi),
        p.1 • f (Complex.polarCoord.symm p) := by
  let A : Set ℂ := {z | ‖z‖ ∈ Icc r R}
  let B : Set (ℝ × ℝ) := Icc r R ×ˢ (univ : Set ℝ)
  have hA : MeasurableSet A := measurableSet_Icc.preimage continuous_norm.measurable
  have hB : MeasurableSet B := measurableSet_Icc.prod MeasurableSet.univ
  rw [← integral_indicator hA, ← Complex.integral_comp_polarCoord_symm]
  have heq : (∫ p in polarCoord.target, p.1 • A.indicator f (Complex.polarCoord.symm p)) =
      ∫ p in polarCoord.target, B.indicator
        (fun p => p.1 • f (Complex.polarCoord.symm p)) p := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    have hp₀ : 0 < p.1 := hp.1
    have he : Complex.polarCoord.symm p ∈ A ↔ p ∈ B := by
      simp [A, B, abs_of_pos hp₀]
    by_cases h : p ∈ B
    · simp only [indicator_of_mem (he.mpr h), indicator_of_mem h]
    · simp only [indicator_of_notMem (mt he.mp h), indicator_of_notMem h, smul_zero]
  rw [heq, setIntegral_indicator hB]
  have hset : polarCoord.target ∩ B = Icc r R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [polarCoord_target, B, mem_inter_iff, mem_prod, mem_Ioi, mem_Icc,
      mem_univ, and_true, mem_Ioo]
    constructor
    · rintro ⟨⟨_, hθ⟩, hp⟩
      exact ⟨hp, hθ⟩
    · rintro ⟨hp, hθ⟩
      exact ⟨⟨hr.trans_le hp.1, hθ⟩, hp⟩
  rw [hset, ← Icc_prod_Icc]
  apply setIntegral_congr_set
  exact Measure.set_prod_ae_eq Filter.EventuallyEq.rfl
    (Ioo_ae_eq_Icc (α := ℝ) (μ := volume))

end DifferentialGeometry.Analysis

end

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Analysis

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

theorem integral_annulus_eq_integral_normalized_polar
    (f : ℂ → ℝ) {r R : ℝ} (hr : 0 < r)
    (hraw : IntegrableOn (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p))
      (Icc r R ×ˢ Icc (-Real.pi) Real.pi))
    (hnorm : IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * f (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)))
      (Icc r R ×ˢ Icc (0 : ℝ) 1)) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f z) =
      (2 * Real.pi) * ∫ p in Icc r R ×ˢ Icc (0 : ℝ) 1,
        p.1 * f (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) := by
  rw [integral_annulus_eq_polar f hr]
  simp only [smul_eq_mul]
  rw [← Icc_prod_Icc]
  rw [Measure.volume_eq_prod] at ⊢ hraw hnorm
  rw [setIntegral_prod _ hraw, setIntegral_prod _ hnorm]
  simp_rw [integral_const_mul, integral_Icc_comp_circle_parameter]
  rw [← integral_const_mul]
  congr 1
  funext ρ
  ring

private theorem integrableOn_mul_comp_polarCoord_of_bounded
    {f : ℂ → ℝ} (hf : Measurable f) {r R B : ℝ} (hr : 0 < r)
    (hbound : ∀ z, ‖z‖ ∈ Icc r R → ‖f z‖ ≤ B)
    {s : Set ℝ} (hs : IsCompact s) (θ : ℝ × ℝ → ℝ) (hθ : Measurable θ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm (p.1, θ p)))
      (Icc r R ×ˢ s) := by
  have hp : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm (p.1, θ p)) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm (p.1, θ p))) :=
    measurable_fst.mul (hf.comp hp)
  apply IntegrableOn.of_bound ((isCompact_Icc.prod hs).measure_lt_top)
    hm.aestronglyMeasurable (|R| * max B 0)
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod hs.measurableSet)] with p hp
  have hρ : 0 ≤ p.1 := hr.le.trans hp.1.1
  have hz : ‖Complex.polarCoord.symm (p.1, θ p)‖ ∈ Icc r R := by
    simpa only [Complex.norm_polarCoord_symm, abs_of_nonneg hρ] using hp.1
  have hρR : ‖p.1‖ ≤ |R| := by
    rw [Real.norm_eq_abs, abs_of_nonneg hρ]
    exact hp.1.2.trans (le_abs_self R)
  rw [norm_mul]
  exact mul_le_mul hρR ((hbound _ hz).trans (le_max_left B 0)) (norm_nonneg _) (abs_nonneg R)

theorem integrableOn_mul_comp_normalized_polar_of_bounded
    {f : ℂ → ℝ} (hf : Measurable f) {r R B : ℝ} (hr : 0 < r)
    (hbound : ∀ z, ‖z‖ ∈ Icc r R → ‖f z‖ ≤ B) :
    IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * f (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)))
      (Icc r R ×ˢ Icc (0 : ℝ) 1) :=
  integrableOn_mul_comp_polarCoord_of_bounded hf hr hbound isCompact_Icc _ (by fun_prop)

theorem integral_annulus_eq_integral_normalized_polar_of_bounded
    {f : ℂ → ℝ} (hf : Measurable f) {r R B : ℝ} (hr : 0 < r)
    (hbound : ∀ z, ‖z‖ ∈ Icc r R → ‖f z‖ ≤ B) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f z) =
      (2 * Real.pi) * ∫ p in Icc r R ×ˢ Icc (0 : ℝ) 1,
        p.1 * f (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) := by
  apply integral_annulus_eq_integral_normalized_polar f hr
  · exact integrableOn_mul_comp_polarCoord_of_bounded hf hr hbound isCompact_Icc
      Prod.snd measurable_snd
  · exact integrableOn_mul_comp_normalized_polar_of_bounded hf hr hbound

end DifferentialGeometry.Analysis

end

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Analysis

private theorem polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]


private theorem continuous_circle_parameter :
    Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi)) := by
  unfold circleMap
  fun_prop

private theorem integrableOn_circle_parameter (g : ℂ → ℝ) (hg : Continuous g)
    (r R : ℝ) :
    Integrable (fun p : ℝ × ℝ => g (circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi)))
      ((volume.restrict (Icc r R)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  exact (hg.comp continuous_circle_parameter).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

theorem integrableOn_integral_circleMap (g : ℂ → ℝ) (hg : Continuous g) (r R : ℝ) :
    IntegrableOn (fun ρ => ∫ t in Icc (0 : ℝ) 1,
      g (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) (Icc r R) :=
  (integrableOn_circle_parameter g hg r R).integral_prod_left

theorem integral_annulus_eq_integral_circleMap (g : ℂ → ℝ) (hg : Continuous g)
    {r R : ℝ} (hr : 0 < r) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, g z) =
      (2 * Real.pi) * ∫ ρ in Icc r R, ρ * ∫ t in Icc (0 : ℝ) 1,
        g (circleMap 0 ρ (2 * Real.pi * t - Real.pi)) := by
  have hc : Continuous (fun p : ℝ × ℝ => p.1 * g (circleMap 0 p.1 p.2)) := by
    apply continuous_fst.mul
    apply hg.comp
    unfold circleMap
    fun_prop
  have hi : IntegrableOn (fun p : ℝ × ℝ => p.1 * g (circleMap 0 p.1 p.2))
      (Icc r R ×ˢ Icc (-Real.pi) Real.pi) (volume.prod volume) :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [integral_annulus_eq_polar g hr]
  simp_rw [polarCoord_symm_eq_circleMap, smul_eq_mul]
  rw [← Icc_prod_Icc, Measure.volume_eq_prod, setIntegral_prod _ hi]
  simp_rw [integral_const_mul, integral_Icc_comp_circle_parameter]
  rw [← integral_const_mul]
  congr 1
  funext ρ
  ring

theorem integral_circleMap_norm_sq_radial_le
    {F : Type*} [SeminormedAddCommGroup F] {f : ℂ → F} (hf : Continuous f)
    {r R : ℝ} (hr : 0 < r) :
    (∫ ρ in Icc r R, ∫ t in Icc (0 : ℝ) 1,
      ‖f (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ ^ 2) ≤
      (2 * Real.pi * r)⁻¹ * ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖f z‖ ^ 2 := by
  let M : ℝ → ℝ := fun ρ => ∫ t in Icc (0 : ℝ) 1,
    ‖f (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ ^ 2
  have hM : IntegrableOn M (Icc r R) :=
    integrableOn_integral_circleMap (fun z => ‖f z‖ ^ 2) (hf.norm.pow 2) r R
  have hρM : IntegrableOn (fun ρ => ρ * M ρ) (Icc r R) := by
    have hc : Continuous (fun p : ℝ × ℝ => p.1 *
        ‖f (circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi))‖ ^ 2) :=
      continuous_fst.mul ((hf.comp continuous_circle_parameter).norm.pow 2)
    have hi : Integrable (fun p : ℝ × ℝ => p.1 *
        ‖f (circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi))‖ ^ 2)
        ((volume.restrict (Icc r R)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
      rw [Measure.prod_restrict]
      exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    simpa only [IntegrableOn, integral_const_mul, M] using hi.integral_prod_left
  have hMnonneg (ρ : ℝ) : 0 ≤ M ρ := integral_nonneg fun _ => sq_nonneg _
  have hle : r * (∫ ρ in Icc r R, M ρ) ≤ ∫ ρ in Icc r R, ρ * M ρ := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hM.const_mul r) hρM measurableSet_Icc
      (fun ρ hρ => mul_le_mul_of_nonneg_right hρ.1 (hMnonneg ρ))
  have heq := integral_annulus_eq_integral_circleMap (fun z => ‖f z‖ ^ 2) (hf.norm.pow 2) (R := R) hr
  change (∫ ρ in Icc r R, M ρ) ≤ _
  rw [heq]
  have hpos : 0 < 2 * Real.pi * r := by positivity
  have hscaled :
      (2 * Real.pi * r) * (∫ ρ in Icc r R, M ρ) ≤
        (2 * Real.pi * r) * ((2 * Real.pi * r)⁻¹ *
          ((2 * Real.pi) * ∫ ρ in Icc r R, ρ * M ρ)) := by
    calc
      (2 * Real.pi * r) * (∫ ρ in Icc r R, M ρ) =
          (2 * Real.pi) * (r * ∫ ρ in Icc r R, M ρ) := by ring
      _ ≤ (2 * Real.pi) * ∫ ρ in Icc r R, ρ * M ρ :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  nlinarith

theorem tendsto_integral_circleMap_norm_sq_radial_zero
    {F : Type*} [SeminormedAddCommGroup F] {f : ℕ → ℂ → F}
    (hf : ∀ n, Continuous (f n)) {r R : ℝ} (hr : 0 < r)
    (hlim : Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖f n z‖ ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ρ in Icc r R, ∫ t in Icc (0 : ℝ) 1,
      ‖f n (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _)
    (fun n => integral_circleMap_norm_sq_radial_le (hf n) hr)
  simpa only [mul_zero] using hlim.const_mul (2 * Real.pi * r)⁻¹

end DifferentialGeometry.Analysis

end

noncomputable section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis




private theorem integral_annulus_eq_integral_circleMap_of_integrable
    (g : ℂ → ℝ) {r R : ℝ} (hr : 0 < r)
    (hi : IntegrableOn (fun p : ℝ × ℝ => p.1 * g (circleMap 0 p.1 p.2))
      (Icc r R ×ˢ Icc (-Real.pi) Real.pi) (volume.prod volume)) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, g z) =
      (2 * Real.pi) * ∫ ρ in Icc r R, ρ * ∫ t in Icc (0 : ℝ) 1,
        g (circleMap 0 ρ (2 * Real.pi * t - Real.pi)) := by
  have hp (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  rw [integral_annulus_eq_polar g hr]
  simp_rw [hp, smul_eq_mul]
  rw [← Icc_prod_Icc, Measure.volume_eq_prod, setIntegral_prod _ hi]
  simp_rw [integral_const_mul, integral_Icc_comp_circle_parameter]
  rw [← integral_const_mul]
  congr 1
  funext ρ
  ring

private theorem norm_deriv_comp_circleMap_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u : ℂ → F}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ)
    (hu : DifferentiableAt ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) :
    ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ≤
      ‖fderiv ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ * (2 * Real.pi * ρ) := by
  have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t - Real.pi) (2 * Real.pi) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const Real.pi
  have hc := (hasDerivAt_circleMap 0 ρ (2 * Real.pi * t - Real.pi)).scomp t hθ
  have hchain := hu.hasFDerivAt.comp_hasDerivAt t hc
  rw [show deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t =
      fderiv ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))
        ((2 * Real.pi) • (circleMap 0 ρ (2 * Real.pi * t - Real.pi) * Complex.I)) from
    hchain.deriv]
  calc
    _ ≤ ‖fderiv ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ *
        ‖(2 * Real.pi) • (circleMap 0 ρ (2 * Real.pi * t - Real.pi) * Complex.I)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by
      simp [abs_of_nonneg hρ, abs_of_pos Real.pi_pos]

private theorem integrableOn_and_integral_norm_sq_deriv_circleMap_radial_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    IntegrableOn (fun ρ => ∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ^ 2) (Icc r R) ∧
    (∫ ρ in Icc r R, ∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤
      (2 * Real.pi * R) * ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ u z‖ ^ 2 := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let μ : Measure ℝ := volume.restrict (Icc r R)
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let q : ℝ × ℝ → ℝ := fun p =>
    ‖deriv (fun t => u (circleMap 0 p.1 (2 * Real.pi * t - Real.pi))) p.2‖ ^ 2
  let b : ℝ × ℝ → ℝ := fun p => (2 * Real.pi) * p.1 *
    ‖fderiv ℝ u (circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi))‖ ^ 2
  have hR : 0 < R := hr.trans_le hrR
  have hqmeas : Measurable q :=
    (stronglyMeasurable_deriv_with_param
      (f := fun ρ t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi)))
      (hu.continuous.comp continuous_circle_parameter)).norm.measurable.pow_const 2
  have hbmeas : Measurable b := by
    apply Measurable.mul
    · exact measurable_const.mul measurable_fst
    · exact ((measurable_fderiv ℝ u).comp continuous_circle_parameter.measurable).norm.pow_const 2
  have hdiff : ∀ᵐ ρ ∂μ, ∀ᵐ t ∂ν,
      DifferentiableAt ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi)) :=
    ae_ae_comp_circleMap_normalized (hu.ae_differentiableAt (μ := volume)) hr
  have hqboundAA : ∀ᵐ ρ ∂μ, ∀ᵐ t ∂ν, ‖q (ρ, t)‖ ≤ ((C : ℝ) * (2 * Real.pi * R)) ^ 2 := by
    filter_upwards [hdiff, ae_restrict_mem measurableSet_Icc] with ρ hρ hρmem
    filter_upwards [hρ] with t ht
    have hρ0 : 0 ≤ ρ := hr.le.trans hρmem.1
    have hd := norm_deriv_comp_circleMap_le hρ0 t ht
    have hnorm := norm_fderiv_le_of_lipschitz ℝ (x₀ := circleMap 0 ρ
      (2 * Real.pi * t - Real.pi)) hu
    have hρR : 2 * Real.pi * ρ ≤ 2 * Real.pi * R := by nlinarith [Real.pi_pos, hρmem.2]
    have hle : ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ≤
        (C : ℝ) * (2 * Real.pi * R) :=
      hd.trans (mul_le_mul hnorm hρR (by positivity) C.coe_nonneg)
    simpa only [q, norm_pow, norm_norm] using
      pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hqbound : ∀ᵐ p ∂μ.prod ν, ‖q p‖ ≤ ((C : ℝ) * (2 * Real.pi * R)) ^ 2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_le hqmeas.norm measurable_const)).mpr
      hqboundAA
  have hqi : Integrable q (μ.prod ν) :=
    Integrable.of_bound hqmeas.aestronglyMeasurable _ hqbound
  have hbi : Integrable b (μ.prod ν) := by
    apply Integrable.of_bound hbmeas.aestronglyMeasurable ((2 * Real.pi * R) * (C : ℝ) ^ 2)
    have hρae : ∀ᵐ p ∂μ.prod ν, p.1 ∈ Icc r R :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hρae] with p hp
    have hρ0 : 0 ≤ p.1 := hr.le.trans hp.1
    have hnorm := norm_fderiv_le_of_lipschitz ℝ (x₀ := circleMap 0 p.1
      (2 * Real.pi * p.2 - Real.pi)) hu
    have hρR : 2 * Real.pi * p.1 ≤ 2 * Real.pi * R := by nlinarith [Real.pi_pos, hp.2]
    dsimp only [b]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hρR (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (sq_nonneg _) (by positivity)
  have hleAA : ∀ᵐ ρ ∂μ, ∀ᵐ t ∂ν, q (ρ, t) ≤ (2 * Real.pi * R) * b (ρ, t) := by
    filter_upwards [hdiff, ae_restrict_mem measurableSet_Icc] with ρ hρ hρmem
    filter_upwards [hρ] with t ht
    have hρ0 : 0 ≤ ρ := hr.le.trans hρmem.1
    have hd := norm_deriv_comp_circleMap_le hρ0 t ht
    have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
    have hrad : ρ ^ 2 ≤ R * ρ := by nlinarith [hρmem.2]
    have hcoef : (2 * Real.pi * ρ) ^ 2 ≤ (2 * Real.pi * R) * (2 * Real.pi * ρ) := by
      nlinarith [mul_nonneg (sq_nonneg (2 * Real.pi)) (sub_nonneg.mpr hrad)]
    calc
      q (ρ, t) ≤ ‖fderiv ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ ^ 2 *
          (2 * Real.pi * ρ) ^ 2 := by simpa only [q, mul_pow] using hs
      _ ≤ ‖fderiv ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ ^ 2 *
          ((2 * Real.pi * R) * (2 * Real.pi * ρ)) :=
        mul_le_mul_of_nonneg_left hcoef (sq_nonneg _)
      _ = _ := by dsimp [b]; ring
  have hleE : ∀ᵐ ρ ∂μ, (∫ t, q (ρ, t) ∂ν) ≤ (2 * Real.pi * R) * ∫ t, b (ρ, t) ∂ν := by
    filter_upwards [hqi.prod_right_ae, hbi.prod_right_ae, hleAA] with ρ hqρ hbρ hle
    simpa only [integral_const_mul] using integral_mono_ae hqρ (hbρ.const_mul (2 * Real.pi * R)) hle
  have hiPolar : IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖fderiv ℝ u (circleMap 0 p.1 p.2)‖ ^ 2)
      (Icc r R ×ˢ Icc (-Real.pi) Real.pi) (volume.prod volume) := by
    have hcir : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
      unfold circleMap
      fun_prop
    have hm : Measurable (fun p : ℝ × ℝ => p.1 * ‖fderiv ℝ u (circleMap 0 p.1 p.2)‖ ^ 2) :=
      measurable_fst.mul (((measurable_fderiv ℝ u).comp hcir.measurable).norm.pow_const 2)
    apply IntegrableOn.of_bound
      ((isCompact_Icc.prod isCompact_Icc).measure_lt_top) hm.aestronglyMeasurable
      (R * (C : ℝ) ^ 2)
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have hρ0 : 0 ≤ p.1 := hr.le.trans hp.1.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hp.1.2
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hu) 2)
      (sq_nonneg _) hR.le
  have heq := integral_annulus_eq_integral_circleMap_of_integrable
    (fun z => ‖fderiv ℝ u z‖ ^ 2) hr hiPolar
  have hbint : (∫ ρ, ∫ t, b (ρ, t) ∂ν ∂μ) =
      ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ u z‖ ^ 2 := by
    rw [heq]
    dsimp only [b, μ, ν]
    simp_rw [integral_const_mul]
    rw [← integral_const_mul]
    congr 1
    funext ρ
    ring
  refine ⟨hqi.integral_prod_left, ?_⟩
  have h := integral_mono_ae hqi.integral_prod_left
    (hbi.integral_prod_left.const_mul (2 * Real.pi * R)) hleE
  rw [integral_const_mul, hbint] at h
  exact h

theorem integrableOn_integral_norm_sq_deriv_circleMap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    IntegrableOn (fun ρ => ∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ^ 2) (Icc r R) :=
  (integrableOn_and_integral_norm_sq_deriv_circleMap_radial_le hu hr hrR).1

theorem integral_norm_sq_deriv_circleMap_radial_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    (∫ ρ in Icc r R, ∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤
      (2 * Real.pi * R) * ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ u z‖ ^ 2 :=
  (integrableOn_and_integral_norm_sq_deriv_circleMap_radial_le hu hr hrR).2

end DifferentialGeometry.Analysis

end
