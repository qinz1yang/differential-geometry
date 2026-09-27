import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory

variable {P X Y : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem MemLp.clm_apply_of_ae_norm_le
    {p : ℝ≥0∞} {A : P → X →L[ℝ] Y}
    (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C)
    {v : P → X} (hv : MemLp v p μ) :
    MemLp (fun t => A t (v t)) p μ := by
  apply hv.of_le_mul (c := C)
    ((ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂
      hv.aestronglyMeasurable hA)
  filter_upwards [hC] with t ht
  exact (A t).le_opNorm (v t) |>.trans
    (mul_le_mul_of_nonneg_right ht (norm_nonneg _))

theorem tendsto_eLpNorm_clm_apply_sub_of_ae_tendsto
    {p : ℝ≥0∞} (hp : p ≠ ∞)
    (A : ℕ → P → X →L[ℝ] Y) (A₀ : P → X →L[ℝ] Y)
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ t ∂μ, ‖A n t‖ ≤ C)
    (hconv : ∀ᵐ t ∂μ, Tendsto (fun n => A n t) atTop (𝓝 (A₀ t)))
    {v : P → X} (hv : MemLp v p μ) :
    Tendsto (fun n => eLpNorm (fun t => (A n t - A₀ t) (v t)) p μ)
      atTop (𝓝 0) := by
  have hA₀ : AEStronglyMeasurable A₀ μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hA hconv
  have hC₀ : ∀ᵐ t ∂μ, ‖A₀ t‖ ≤ C := by
    filter_upwards [hconv, ae_all_iff.mpr hC] with t ht hb
    exact le_of_tendsto ht.norm (Eventually.of_forall hb)
  by_cases hp₀ : p = 0
  · simp only [hp₀, eLpNorm_exponent_zero]
    exact tendsto_const_nhds
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp
  let D : ℝ := 2 * max 0 C
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (le_max_left _ _)
  let f : ℕ → P → Y := fun n t => (A n t - A₀ t) (v t)
  let b : P → X := fun t => D • v t
  have hb : MemLp b p μ := hv.const_smul D
  have hf (n : ℕ) : AEStronglyMeasurable (f n) μ :=
    (ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂
      hv.aestronglyMeasurable ((hA n).sub hA₀)
  have hbound (n : ℕ) : ∀ᵐ t ∂μ, ‖f n t‖ₑ ≤ ‖b t‖ₑ := by
    filter_upwards [hC n, hC₀] with t ht ht₀
    apply enorm_le_iff_norm_le.mpr
    have hnorm : ‖A n t - A₀ t‖ ≤ D := by
      calc
        _ ≤ ‖A n t‖ + ‖A₀ t‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add ht ht₀
        _ ≤ D := by dsimp only [D]; linarith [le_max_right (0 : ℝ) C]
    calc
      ‖f n t‖ ≤ ‖A n t - A₀ t‖ * ‖v t‖ :=
        (A n t - A₀ t).le_opNorm (v t)
      _ ≤ D * ‖v t‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = ‖b t‖ := by simp only [b, norm_smul, Real.norm_of_nonneg hD]
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun n => f n t) atTop (𝓝 0) := by
    filter_upwards [hconv] with t ht
    have hsub : Tendsto (fun n => A n t - A₀ t) atTop
        (𝓝 (0 : X →L[ℝ] Y)) := by
      simpa only [sub_self] using ht.sub (tendsto_const_nhds (x := A₀ t))
    simpa only [Function.comp_def, f, ContinuousLinearMap.apply_apply, map_zero] using
      ((ContinuousLinearMap.apply ℝ Y (v t)).continuous.tendsto 0).comp hsub
  have hpowlim : ∀ᵐ t ∂μ,
      Tendsto (fun n => ‖f n t‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    filter_upwards [hlim] with t ht
    have hnormlim : Tendsto (fun n => ‖f n t‖ₑ) atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa only [enorm_zero] using ht.enorm
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos hpr] using
      (ENNReal.continuous_rpow_const (y := p.toReal)).continuousAt.tendsto.comp hnormlim
  have hlin : Tendsto (fun n => ∫⁻ t, ‖f n t‖ₑ ^ p.toReal ∂μ)
      atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence'
        (fun t => ‖b t‖ₑ ^ p.toReal)
        (fun n => (hf n).enorm.pow_const p.toReal)
        (fun n => (hbound n).mono fun t ht => ENNReal.rpow_le_rpow ht hpr.le)
        (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ hp hb.eLpNorm_lt_top).ne
        hpowlim
  change Tendsto (fun n => eLpNorm (f n) p μ) atTop (𝓝 0)
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp]
  simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpr)] using
    (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).continuousAt.tendsto.comp hlin


end MeasureTheory
