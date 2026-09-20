import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis

theorem ae_comp_polarCoord_symm {P : ℂ → Prop} (hP : ∀ᵐ z : ℂ, P z) :
    ∀ᵐ p : ℝ × ℝ ∂volume.restrict polarCoord.target,
      P (Complex.polarCoord.symm p) := by
  let N := toMeasurable volume {z : ℂ | ¬ P z}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN : volume N = 0 := by
    rw [show N = toMeasurable volume {z : ℂ | ¬ P z} from rfl, measure_toMeasurable]
    exact ae_iff.mp hP
  let f : ℂ → ℝ≥0∞ := N.indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator hNm
  have hpolar : Continuous (Complex.polarCoord.symm : ℝ × ℝ → ℂ) :=
    Complex.equivRealProdCLM.symm.continuous.comp continuous_polarCoord_symm
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul (hfm.comp hpolar.measurable)
  have hzero : (∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p)) = 0 := by
    rw [show (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p)) =
      (fun p => ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) from rfl,
      Complex.lintegral_comp_polarCoord_symm]
    exact (lintegral_indicator_one hNm).trans hN
  have hae := (lintegral_eq_zero_iff hmeas).mp hzero
  filter_upwards [hae, self_mem_ae_restrict polarCoord.open_target.measurableSet] with p hp hpt
  have hpos : ENNReal.ofReal p.1 ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpt.1)
  have hfzero : f (Complex.polarCoord.symm p) = 0 :=
    (mul_eq_zero.mp hp).resolve_left hpos
  by_contra hbad
  have hmem : Complex.polarCoord.symm p ∈ N :=
    subset_toMeasurable volume {z : ℂ | ¬ P z} hbad
  simp only [f, indicator_of_mem hmem, one_ne_zero] at hfzero

theorem ae_ae_comp_circleMap {P : ℂ → Prop} (hP : ∀ᵐ z : ℂ, P z) :
    ∀ᵐ ρ ∂volume.restrict (Ioi (0 : ℝ)), ∀ᵐ θ ∂volume.restrict (Icc (-Real.pi) Real.pi),
      P (circleMap 0 ρ θ) := by
  have hbase := ae_comp_polarCoord_symm hP
  change (∀ᵐ x : ℝ × ℝ ∂volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi),
      P (Complex.polarCoord.symm x)) at hbase
  have hae : ∀ᵐ x : ℝ × ℝ ∂(volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi)), P (Complex.polarCoord.symm x) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hbase
  have hslices := Measure.ae_ae_of_ae_prod hae
  filter_upwards [hslices] with ρ hρ
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hρ
  simpa only [Complex.polarCoord_symm_apply, circleMap_zero,
    Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin] using hρ

theorem _root_.LipschitzWith.ae_ae_differentiableAt_circleMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℂ → E} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ ρ ∂volume.restrict (Ioi (0 : ℝ)), ∀ᵐ θ ∂volume.restrict (Icc (-Real.pi) Real.pi),
      DifferentiableAt ℝ f (circleMap 0 ρ θ) :=
  ae_ae_comp_circleMap hf.ae_differentiableAt

end DifferentialGeometry.Analysis

end

noncomputable section

open Set MeasureTheory Filter

open scoped ENNReal

namespace DifferentialGeometry.Analysis

theorem ae_ae_comp_polarCoord_symm {P : ℂ → Prop} (hP : ∀ᵐ z ∂volume, P z)
    {r R : ℝ} (hr : 0 < r) :
    ∀ᵐ ρ ∂volume.restrict (Icc r R),
      ∀ᵐ θ ∂volume.restrict (Icc (-Real.pi) Real.pi),
        P (Complex.polarCoord.symm (ρ, θ)) := by
  have hs : Icc r R ×ˢ Ioo (-Real.pi) Real.pi ⊆ polarCoord.target := by
    rintro ⟨ρ, θ⟩ ⟨hρ, hθ⟩
    exact ⟨hr.trans_le hρ.1, hθ⟩
  have h := ae_restrict_of_ae_restrict_of_subset hs (ae_comp_polarCoord_symm hP)
  have heq : Icc r R ×ˢ Ioo (-Real.pi) Real.pi =ᵐ[volume]
      Icc r R ×ˢ Icc (-Real.pi) Real.pi := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq EventuallyEq.rfl Ioo_ae_eq_Icc
  rw [Measure.restrict_congr_set heq, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  exact Measure.ae_ae_of_ae_prod h

end DifferentialGeometry.Analysis

end

noncomputable section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis

theorem ae_ae_comp_circleMap_normalized {P : ℂ → Prop} (hP : ∀ᵐ z ∂volume, P z)
    {r R : ℝ} (hr : 0 < r) :
    ∀ᵐ ρ ∂volume.restrict (Icc r R), ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      P (circleMap 0 ρ (2 * Real.pi * t - Real.pi)) := by
  have hq : Measure.QuasiMeasurePreserving (fun t : ℝ => 2 * Real.pi * t - Real.pi)
      volume volume := by
    simpa only [Function.comp_def, smul_eq_mul, sub_eq_add_neg] using
      ((measurePreserving_add_right volume (-Real.pi)).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_smul volume (show 2 * Real.pi ≠ 0 by positivity)))
  have hqr := hq.restrict (s := Icc (0 : ℝ) 1) (t := Icc (-Real.pi) Real.pi) (by
    intro t ht
    constructor <;> nlinarith [Real.pi_pos, ht.1, ht.2])
  filter_upwards [ae_ae_comp_polarCoord_symm hP hr] with ρ hρ
  have h := hqr.ae hρ
  have hp (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  simpa only [hp] using h

end DifferentialGeometry.Analysis

end
