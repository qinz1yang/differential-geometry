/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Calculus.Quasiconformal.MetricDifferentiability

noncomputable section

open Set Filter Metric MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal

namespace DifferentialGeometry.DirectionalEnergy

open MetricDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem ae_norm_fderiv_pow_le_density (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E ≃ₜ E) {H : ℝ} (hH : 0 < H)
    (hf : ∀ x y z : E, dist y x ≤ dist z x →
      dist (f y) (f x) ≤ H * dist (f z) (f x))
    (v : E) (hv : ‖v‖ ≤ 1) :
    ∀ᵐ x ∂μ, ‖fderiv ℝ f x v‖ ^ Module.finrank ℝ E ≤
      H ^ Module.finrank ℝ E * ((imageMeasure μ f).rnDeriv μ x).toReal := by
  have hglobal : HasGlobalDistortion f := ⟨H, hH, hf⟩
  filter_upwards [ae_differentiableAt μ f hglobal.local,
    Besicovitch.ae_tendsto_rnDeriv (imageMeasure μ f) μ,
    Measure.rnDeriv_lt_top (imageMeasure μ f) μ] with x hdx hden hfin
  have hd := ((hdx.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right.norm).pow
    (Module.finrank ℝ E)
  have ht := ((ENNReal.continuousAt_toReal hfin.ne).tendsto.comp hden).const_mul
    (H ^ Module.finrank ℝ E)
  apply le_of_tendsto_of_tendsto hd ht
  filter_upwards [self_mem_nhdsWithin] with h hpos
  have hh : 0 < h := hpos
  have hc : 0 < (μ (ball (0 : E) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 zero_lt_one).ne' measure_ball_lt_top.ne
  have hb := displacement_pow_le_imageMeasure μ f hH hf x (x + h • v) hh (by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_of_le_one_right hh.le hv)
  have hdiv := div_le_div_of_nonneg_right hb
    (pow_nonneg hh.le (Module.finrank ℝ E))
  have he : ‖h⁻¹ • (f (x + h • v) - f x)‖ ^ Module.finrank ℝ E =
      dist (f (x + h • v)) (f x) ^ Module.finrank ℝ E /
        h ^ Module.finrank ℝ E := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh),
      dist_eq_norm, mul_pow, inv_pow]
    ring
  simp only [Function.comp_apply]
  rw [he, ENNReal.toReal_div, addHaar_closedBall μ x hh.le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hh.le _)]
  convert hdiv using 1
  field_simp

def density (f : E → E) (v : E) (x : E) : ℝ≥0∞ :=
  ENNReal.ofReal (‖fderiv ℝ f x v‖ ^ Module.finrank ℝ E)

omit [Nontrivial E] in
theorem measurable_density (f : E → E) (v : E) : Measurable (density f v) :=
  ((measurable_fderiv_apply_const ℝ f v).norm.pow_const _).ennreal_ofReal

def energyMeasure (μ : Measure E) (f : E → E) (v : E) : Measure E :=
  μ.withDensity (density f v)

omit [FiniteDimensional ℝ E] [BorelSpace E] [Nontrivial E] in
theorem energyMeasure_absolutelyContinuous (μ : Measure E) (f : E → E) (v : E) :
    energyMeasure μ f v ≪ μ :=
  withDensity_absolutelyContinuous μ (density f v)

theorem energyMeasure_le_imageMeasure (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E ≃ₜ E) {H : ℝ} (hH : 0 < H)
    (hf : ∀ x y z : E, dist y x ≤ dist z x →
      dist (f y) (f x) ≤ H * dist (f z) (f x))
    (v : E) (hv : ‖v‖ ≤ 1) :
    energyMeasure μ f v ≤ ENNReal.ofReal (H ^ Module.finrank ℝ E) • imageMeasure μ f := by
  have hbound : density f v ≤ᵐ[μ]
      ENNReal.ofReal (H ^ Module.finrank ℝ E) • (imageMeasure μ f).rnDeriv μ := by
    filter_upwards [ae_norm_fderiv_pow_le_density μ f hH hf v hv,
      Measure.rnDeriv_lt_top (imageMeasure μ f) μ] with x hx hfin
    change ENNReal.ofReal (‖fderiv ℝ f x v‖ ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (H ^ Module.finrank ℝ E) * (imageMeasure μ f).rnDeriv μ x
    convert ENNReal.ofReal_le_ofReal hx using 1
    rw [ENNReal.ofReal_mul (pow_nonneg hH.le _), ENNReal.ofReal_toReal hfin.ne]
  have h := withDensity_mono hbound
  rw [withDensity_smul _ (Measure.measurable_rnDeriv _ _)] at h
  apply h.trans
  exact _root_.smul_le_smul_left _ (withDensity_rnDeriv_le (imageMeasure μ f) μ)

theorem energyMeasure_isLocallyFinite (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E ≃ₜ E) (hf : HasGlobalDistortion f) (v : E) (hv : ‖v‖ ≤ 1) :
    IsLocallyFiniteMeasure (energyMeasure μ f v) := by
  obtain ⟨H, hH, hcomp⟩ := hf
  let : IsFiniteMeasureOnCompacts
      (ENNReal.ofReal (H ^ Module.finrank ℝ E) • imageMeasure μ f) :=
    IsFiniteMeasureOnCompacts.smul (imageMeasure μ f) ENNReal.ofReal_ne_top
  exact isLocallyFiniteMeasure_of_le (energyMeasure_le_imageMeasure μ f hH hcomp v hv)

end DifferentialGeometry.DirectionalEnergy
