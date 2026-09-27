import DifferentialGeometry.Analysis.Integration.Measure.Polar.Complex
import DifferentialGeometry.Analysis.Integration.PolarAnnulus.Centered
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def circleTangentialEnergy (f : ℂ → E) (Ω : Set ℂ) (c : ℂ) (ρ : ℝ) : ℝ :=
  ∫ θ in Icc (-Real.pi) Real.pi,
    Ω.indicator (fun z => ρ⁻¹ *
      ‖fderiv ℝ f z (circleMap 0 ρ θ * Complex.I)‖ ^ 2) (circleMap c ρ θ)

theorem tangential_energy_le {ρ θ : ℝ} (hρ : 0 < ρ) (A : ℂ →L[ℝ] E) :
    ρ⁻¹ * ‖A (circleMap 0 ρ θ * Complex.I)‖ ^ 2 ≤ ρ * ‖A‖ ^ 2 := by
  have hnorm : ‖A (circleMap 0 ρ θ * Complex.I)‖ ≤ ‖A‖ * ρ := by
    simpa [abs_of_pos hρ] using A.le_opNorm (circleMap 0 ρ θ * Complex.I)
  calc
    _ ≤ ρ⁻¹ * (‖A‖ * ρ) ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hρ.le)).2 hnorm)
        (inv_nonneg.mpr hρ.le)
    _ = ρ * ‖A‖ ^ 2 := by field_simp

theorem integrableOn_circleTangentialEnergy_and_integral_le
    [CompleteSpace E]
    {f : ℂ → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (c : ℂ)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    IntegrableOn (circleTangentialEnergy f Ω c) (Icc r R) ∧
      (∀ ρ ∈ Icc r R, 0 ≤ circleTangentialEnergy f Ω c ρ) ∧
      (∫ ρ in Icc r R, circleTangentialEnergy f Ω c ρ) ≤
        ∫ z in {z : ℂ | dist z c ∈ Icc r R} ∩ Ω, ‖fderiv ℝ f z‖ ^ 2 := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let S : Set (ℝ × ℝ) := {p | circleMap c p.1 p.2 ∈ Ω}
  let A : ℝ × ℝ → ℝ := S.indicator (fun p => p.1⁻¹ *
    ‖fderiv ℝ f (circleMap c p.1 p.2) (circleMap 0 p.1 p.2 * Complex.I)‖ ^ 2)
  let D : ℝ × ℝ → ℝ := S.indicator (fun p =>
    p.1 * ‖fderiv ℝ f (circleMap c p.1 p.2)‖ ^ 2)
  have hc : Continuous (fun p : ℝ × ℝ => circleMap c p.1 p.2) := by
    simp only [circleMap]
    fun_prop
  have hc₀ : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    simp only [circleMap]
    fun_prop
  have hS : MeasurableSet S := hΩ.preimage hc.measurable
  have hDm : Measurable (fun p : ℝ × ℝ =>
      p.1 * ‖fderiv ℝ f (circleMap c p.1 p.2)‖ ^ 2) :=
    measurable_fst.mul (((measurable_fderiv ℝ f).comp hc.measurable).norm.pow_const 2)
  have hAm : Measurable A := by
    apply Measurable.indicator _ hS
    apply Measurable.mul measurable_fst.inv
    have happ : Measurable (fun p : ℝ × ℝ =>
        fderiv ℝ f (circleMap c p.1 p.2) (circleMap 0 p.1 p.2 * Complex.I)) :=
      (isBoundedBilinearMap_apply.continuous.measurable).comp
        (((measurable_fderiv ℝ f).comp hc.measurable).prodMk
          (hc₀.measurable.mul measurable_const))
    exact happ.norm.pow_const 2
  have hAnonneg (p : ℝ × ℝ) (hp : 0 < p.1) : 0 ≤ A p := by
    by_cases h : p ∈ S
    · simp only [A, indicator_of_mem h]
      positivity
    · simp only [A, indicator_of_notMem h, le_refl]
  have hAD : ∀ p ∈ Icc (r, -Real.pi) (R, Real.pi), A p ≤ D p := by
    intro p hp
    by_cases h : p ∈ S
    · simp only [A, D, indicator_of_mem h]
      exact tangential_energy_le (hr.trans_le hp.1.1) _
    · simp only [A, D, indicator_of_notMem h, le_refl]
  have hDi : IntegrableOn D (Icc (r, -Real.pi) (R, Real.pi)) := by
    apply Integrable.indicator _ hS
    apply (integrableOn_const (C := R * (K : ℝ) ^ 2) isCompact_Icc.measure_ne_top).mono'
      hDm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
    have hp0 : 0 ≤ p.1 := (hr.trans_le hp.1.1).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 (sq_nonneg _))]
    exact mul_le_mul hp.2.1
      ((sq_le_sq₀ (norm_nonneg _) K.coe_nonneg).2 (norm_fderiv_le_of_lipschitz ℝ hf))
      (sq_nonneg _) (hr.trans_le hrR).le
  have hAi : IntegrableOn A (Icc (r, -Real.pi) (R, Real.pi)) := by
    apply hDi.mono' hAm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (hAnonneg p (hr.trans_le hp.1.1))]
    exact hAD p hp
  have hAprod : Integrable A
      ((volume.restrict (Icc r R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, Icc_prod_Icc]
    exact hAi
  have hd (ρ : ℝ) : circleTangentialEnergy f Ω c ρ =
      ∫ θ in Icc (-Real.pi) Real.pi, A (ρ, θ) := by
    rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hAprod.integral_prod_left
  · intro ρ hρ
    rw [hd]
    exact integral_nonneg fun θ => hAnonneg (ρ, θ) (hr.trans_le hρ.1)
  · simp_rw [hd]
    rw [← setIntegral_indicator hΩ, integral_annulus_eq_circleMap _ c hr]
    have hleft : (∫ p in Icc (r, -Real.pi) (R, Real.pi), A p) =
        ∫ ρ in Icc r R, ∫ θ in Icc (-Real.pi) Real.pi, A (ρ, θ) := by
      rw [← Icc_prod_Icc, Measure.volume_eq_prod,
        setIntegral_prod A (by rwa [← Measure.volume_eq_prod, Icc_prod_Icc])]
    rw [← hleft]
    have heq : (fun p : ℝ × ℝ =>
        p.1 • Ω.indicator (fun z => ‖fderiv ℝ f z‖ ^ 2) (circleMap c p.1 p.2)) = D := by
      funext p
      by_cases hp : p ∈ S
      · have hpΩ : circleMap c p.1 p.2 ∈ Ω := hp
        simp only [D, indicator_of_mem hp, indicator_of_mem hpΩ, smul_eq_mul]
      · have hpΩ : circleMap c p.1 p.2 ∉ Ω := hp
        simp only [D, indicator_of_notMem hp, indicator_of_notMem hpΩ, smul_zero]
    rw [heq]
    apply integral_mono_ae hAi hDi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
    exact hAD p hp

theorem ae_circle_arc_deriv_integral_le
    [FiniteDimensional ℝ E]
    {f : ℂ → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (c : ℂ) :
    ∀ᵐ ρ ∂volume.restrict (Ioi (0 : ℝ)),
      (∀ᵐ θ ∂volume.restrict (Icc (-Real.pi) Real.pi),
        DifferentiableAt ℝ f (circleMap c ρ θ) ∧
          deriv (f ∘ circleMap c ρ) θ =
            fderiv ℝ f (circleMap c ρ θ) (circleMap 0 ρ θ * Complex.I)) ∧
      ∀ a ∈ Icc (-Real.pi) Real.pi, ∀ b ∈ Icc (-Real.pi) Real.pi,
        a ≤ b → MapsTo (circleMap c ρ) (Icc a b) Ω →
          (∫ θ in Icc a b, ‖deriv (f ∘ circleMap c ρ) θ‖ ^ 2) ≤
            ρ * circleTangentialEnergy f Ω c ρ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  have hshift : ∀ᵐ z : ℂ, DifferentiableAt ℝ f (c + z) :=
    (measurePreserving_add_left (volume : Measure ℂ) c).quasiMeasurePreserving.tendsto_ae.eventually
      hf.ae_differentiableAt
  have hdiff : ∀ᵐ ρ ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ᵐ θ ∂volume.restrict (Icc (-Real.pi) Real.pi),
        DifferentiableAt ℝ f (circleMap c ρ θ) := by
    simpa only [circleMap, zero_add] using ae_ae_comp_circleMap hshift
  filter_upwards [hdiff, ae_restrict_mem measurableSet_Ioi] with ρ hρdiff hρpos
  change 0 < ρ at hρpos
  have hchain : ∀ᵐ θ ∂volume.restrict (Icc (-Real.pi) Real.pi),
      deriv (f ∘ circleMap c ρ) θ =
        fderiv ℝ f (circleMap c ρ θ) (circleMap 0 ρ θ * Complex.I) := by
    filter_upwards [hρdiff] with θ hθ
    rw [fderiv_comp_deriv θ hθ (differentiable_circleMap _ _ _), deriv_circleMap]
  refine ⟨hρdiff.and hchain, ?_⟩
  let A : ℝ → ℝ := fun θ => Ω.indicator (fun z => ρ⁻¹ *
    ‖fderiv ℝ f z (circleMap 0 ρ θ * Complex.I)‖ ^ 2) (circleMap c ρ θ)
  let S : Set ℝ := (circleMap c ρ) ⁻¹' Ω
  have hS : MeasurableSet S := hΩ.preimage (continuous_circleMap c ρ).measurable
  have htrace := hf.comp (lipschitzWith_circleMap c ρ)
  have hderiv : MemLp (deriv (f ∘ circleMap c ρ)) 2
      (volume.restrict (Icc (-Real.pi) Real.pi)) := by
    apply (memLp_const ((K * Real.nnabs ρ : ℝ≥0) : ℝ)).of_le
      (measurable_deriv (f ∘ circleMap c ρ)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun θ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (K * Real.nnabs ρ).coe_nonneg] using
        norm_deriv_le_of_lipschitz htrace (x₀ := θ)
  have hAi : IntegrableOn A (Icc (-Real.pi) Real.pi) := by
    apply ((hderiv.norm.integrable_sq.const_mul ρ⁻¹).indicator hS).congr
    filter_upwards [hchain] with θ hθ
    by_cases hmem : circleMap c ρ θ ∈ Ω
    · have hmem' : θ ∈ S := hmem
      simp only [A, indicator_of_mem hmem, indicator_of_mem hmem', hθ]
    · have hmem' : θ ∉ S := hmem
      simp only [A, indicator_of_notMem hmem, indicator_of_notMem hmem']
  have hAnonneg (θ : ℝ) : 0 ≤ A θ := by
    by_cases hmem : circleMap c ρ θ ∈ Ω
    · simp only [A, indicator_of_mem hmem]
      positivity
    · simp only [A, indicator_of_notMem hmem, le_refl]
  intro a ha b hb hab harc
  have hsub : Icc a b ⊆ Icc (-Real.pi) Real.pi := Icc_subset_Icc ha.1 hb.2
  have heq : (∫ θ in Icc a b, ‖deriv (f ∘ circleMap c ρ) θ‖ ^ 2) =
      ρ * ∫ θ in Icc a b, A θ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hchain.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub)),
      ae_restrict_mem measurableSet_Icc] with θ hθ hθab
    rw [hθ]
    simp only [A, indicator_of_mem (harc hθab), ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hρpos), one_mul]
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ hρpos.le
  exact setIntegral_mono_set hAi (Filter.Eventually.of_forall hAnonneg)
    (Filter.Eventually.of_forall hsub)

end DifferentialGeometry.Analysis

end
