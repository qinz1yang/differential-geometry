import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Measure

variable {X : Type*} [MeasurableSpace X]

theorem integrable_exp_and_integral_le_of_exponential_tail
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : AEMeasurable f μ)
    {decay moment bound : ℝ}
    (hmoment : 0 < moment) (hmoment_decay : moment < decay)
    (hbound : 0 ≤ bound)
    (htail : ∀ level : ℝ, 0 < level →
      μ {x | level < f x} ≤
        ENNReal.ofReal (bound * Real.exp (-decay * level))) :
    Integrable (fun x => Real.exp (moment * f x)) μ ∧
      (∫ x, Real.exp (moment * f x) ∂μ) ≤
        μ.real univ + bound * moment / (decay - moment) := by
  let v : X → ℝ := fun x => max (f x) 0
  let q : X → ℝ := fun x => Real.exp (moment * v x) - 1
  let majorant : ℝ → ℝ := fun level =>
    bound * moment * Real.exp (-(decay - moment) * level)
  have hv_nonneg : ∀ x, 0 ≤ v x := fun x => by
    exact le_max_right _ _
  have hv_meas : AEMeasurable v μ := hf.max aemeasurable_const
  have hg_integrable_interval : ∀ a b : ℝ,
      IntervalIntegrable (fun t => moment * Real.exp (moment * t)) volume a b := by
    intro a b
    exact (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
        (μ := volume) a b
  have hg_integrable : ∀ level > 0,
      IntervalIntegrable (fun t => moment * Real.exp (moment * t)) volume 0 level := by
    intro level hlevel
    exact hg_integrable_interval 0 level
  have hg_nonneg : ∀ᵐ t ∂volume.restrict (Ioi 0),
      0 ≤ moment * Real.exp (moment * t) := by
    exact ae_of_all _ fun t => mul_nonneg hmoment.le (Real.exp_pos _).le
  have hprimitive : ∀ x,
      (∫ t in 0..v x, moment * Real.exp (moment * t)) = q x := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => by
        simpa only [id_eq, mul_one, mul_comm] using
          (((hasDerivAt_id t).const_mul moment).exp))
      (hg_integrable_interval 0 (v x))]
    simp only [q, mul_zero, Real.exp_zero, v]
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (ae_of_all μ hv_nonneg) hv_meas hg_integrable hg_nonneg
  simp_rw [hprimitive] at hlayer
  have hv_tail : ∀ level : ℝ, 0 < level →
      {x | level < v x} = {x | level < f x} := by
    intro level hlevel
    ext x
    constructor
    · intro hx
      change level < max (f x) 0 at hx
      change level < f x
      rcases lt_max_iff.mp hx with hx | hx
      · exact hx
      · exact (not_lt_of_ge hlevel.le hx).elim
    · intro hx
      change level < f x at hx
      change level < max (f x) 0
      exact lt_max_of_lt_left hx
  have hmajorant_nonneg : ∀ level, 0 ≤ majorant level := fun level => by
    exact mul_nonneg (mul_nonneg hbound hmoment.le) (Real.exp_pos _).le
  have hpointwise : ∀ level ∈ Ioi (0 : ℝ),
      μ {x | level < v x} *
          ENNReal.ofReal (moment * Real.exp (moment * level)) ≤
        ENNReal.ofReal (majorant level) := by
    intro level hlevel
    rw [hv_tail level hlevel]
    calc
      μ {x | level < f x} *
            ENNReal.ofReal (moment * Real.exp (moment * level)) ≤
          ENNReal.ofReal (bound * Real.exp (-decay * level)) *
            ENNReal.ofReal (moment * Real.exp (moment * level)) := by
        gcongr
        exact htail level hlevel
      _ = ENNReal.ofReal
          ((bound * Real.exp (-decay * level)) *
            (moment * Real.exp (moment * level))) := by
        exact (ENNReal.ofReal_mul
          (mul_nonneg hbound (Real.exp_pos _).le)).symm
      _ = ENNReal.ofReal (majorant level) := by
        congr 1
        dsimp only [majorant]
        calc
          (bound * Real.exp (-decay * level)) *
              (moment * Real.exp (moment * level)) =
            bound * moment *
              (Real.exp (-decay * level) * Real.exp (moment * level)) := by
                ring
          _ = bound * moment *
              Real.exp (-(decay - moment) * level) := by
                rw [← Real.exp_add]
                congr 2
                ring
  have hgap : 0 < decay - moment := sub_pos.mpr hmoment_decay
  have hmajorant_integrable : IntegrableOn majorant (Ioi 0) := by
    have hexp := integrableOn_exp_mul_Ioi (a := -(decay - moment)) (by linarith) 0
    have hscaled := hexp.const_mul (bound * moment)
    simpa only [majorant, neg_mul] using hscaled
  have hmajorant_integral :
      (∫ level in Ioi 0, majorant level) =
        bound * moment / (decay - moment) := by
    dsimp only [majorant]
    rw [integral_const_mul,
      integral_exp_mul_Ioi (a := -(decay - moment)) (by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [hgap.ne']
  have hlintegral_bound :
      (∫⁻ x, ENNReal.ofReal (q x) ∂μ) ≤
        ENNReal.ofReal (bound * moment / (decay - moment)) := by
    calc
      (∫⁻ x, ENNReal.ofReal (q x) ∂μ) =
          ∫⁻ level in Ioi 0,
            μ {x | level < v x} *
              ENNReal.ofReal (moment * Real.exp (moment * level)) := hlayer
      _ ≤ ∫⁻ level in Ioi 0, ENNReal.ofReal (majorant level) := by
        exact setLIntegral_mono
          (by fun_prop) hpointwise
      _ = ENNReal.ofReal (∫ level in Ioi 0, majorant level) := by
        exact (ofReal_integral_eq_lintegral_ofReal hmajorant_integrable
          (ae_of_all _ hmajorant_nonneg)).symm
      _ = ENNReal.ofReal (bound * moment / (decay - moment)) := by
        rw [hmajorant_integral]
  have hq_nonneg : ∀ x, 0 ≤ q x := by
    intro x
    dsimp only [q]
    rw [sub_nonneg, Real.one_le_exp_iff]
    exact mul_nonneg hmoment.le (hv_nonneg x)
  have hq_meas : AEStronglyMeasurable q μ := by
    exact ((aemeasurable_const.mul hv_meas).exp.sub aemeasurable_const).aestronglyMeasurable
  have hq_finite : HasFiniteIntegral q μ := by
    rw [hasFiniteIntegral_iff_norm]
    have hnorm : (fun x => ENNReal.ofReal ‖q x‖) =
        fun x => ENNReal.ofReal (q x) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hq_nonneg x)]
    rw [hnorm]
    exact hlintegral_bound.trans_lt ENNReal.ofReal_lt_top
  have hq_integrable : Integrable q μ := ⟨hq_meas, hq_finite⟩
  have hconstant_integrable : Integrable (fun _ : X => (1 : ℝ)) μ := integrable_const 1
  have hv_exp_integrable : Integrable (fun x => Real.exp (moment * v x)) μ := by
    have hadd := hq_integrable.add hconstant_integrable
    apply hadd.congr
    exact ae_of_all μ fun x => by
      change (Real.exp (moment * v x) - 1) + 1 = Real.exp (moment * v x)
      ring
  have hf_exp_meas : AEStronglyMeasurable (fun x => Real.exp (moment * f x)) μ :=
    ((aemeasurable_const.mul hf).exp).aestronglyMeasurable
  have hf_exp_le : ∀ x,
      Real.exp (moment * f x) ≤ Real.exp (moment * v x) := by
    intro x
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hmoment.le
  have hf_exp_integrable : Integrable (fun x => Real.exp (moment * f x)) μ := by
    exact hv_exp_integrable.mono hf_exp_meas
      (ae_of_all μ fun x => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hf_exp_le x)
  have hq_integral :
      (∫ x, q x ∂μ) ≤ bound * moment / (decay - moment) := by
    rw [← ENNReal.ofReal_le_ofReal_iff
      (div_nonneg (mul_nonneg hbound hmoment.le) hgap.le)]
    rw [ofReal_integral_eq_lintegral_ofReal hq_integrable (ae_of_all μ hq_nonneg)]
    exact hlintegral_bound
  refine ⟨hf_exp_integrable, ?_⟩
  calc
    (∫ x, Real.exp (moment * f x) ∂μ) ≤
        ∫ x, Real.exp (moment * v x) ∂μ :=
      integral_mono hf_exp_integrable hv_exp_integrable hf_exp_le
    _ = (∫ x, q x ∂μ) + μ.real univ := by
      rw [show (fun x => Real.exp (moment * v x)) = fun x => q x + 1 from by
        funext x
        simp only [q, sub_add_cancel], integral_add hq_integrable hconstant_integrable,
          integral_const, smul_eq_mul, mul_one]
    _ ≤ μ.real univ + bound * moment / (decay - moment) := by
      linarith

theorem integrable_exp_of_exponential_tail
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : AEMeasurable f μ)
    {decay moment bound : ℝ}
    (hmoment : 0 < moment) (hmoment_decay : moment < decay)
    (hbound : 0 ≤ bound)
    (htail : ∀ level : ℝ, 0 < level →
      μ {x | level < f x} ≤
        ENNReal.ofReal (bound * Real.exp (-decay * level))) :
    Integrable (fun x => Real.exp (moment * f x)) μ :=
  (integrable_exp_and_integral_le_of_exponential_tail μ f hf
    hmoment hmoment_decay hbound htail).1

theorem integral_exp_le_of_exponential_tail
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : AEMeasurable f μ)
    {decay moment bound : ℝ}
    (hmoment : 0 < moment) (hmoment_decay : moment < decay)
    (hbound : 0 ≤ bound)
    (htail : ∀ level : ℝ, 0 < level →
      μ {x | level < f x} ≤
        ENNReal.ofReal (bound * Real.exp (-decay * level))) :
    (∫ x, Real.exp (moment * f x) ∂μ) ≤
      μ.real univ + bound * moment / (decay - moment) :=
  (integrable_exp_and_integral_le_of_exponential_tail μ f hf
    hmoment hmoment_decay hbound htail).2

end DifferentialGeometry.Analysis.Measure

end
