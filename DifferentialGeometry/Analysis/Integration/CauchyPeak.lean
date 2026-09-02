import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.PeakFunction

set_option autoImplicit false

noncomputable section

open Bornology Complex Filter MeasureTheory Real Set
open scoped Topology

namespace DifferentialGeometry.Analysis.Integration

def cauchyPeak (z : Complex) : Real :=
  (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)⁻¹

private theorem integral_radial_cauchyPeak :
    ∫ r in Ioi (0 : Real), r * (1 + r ^ 2)⁻¹ ^ 2 = 1 / 2 := by
  let F : Real → Real := fun r => -(1 / 2) * (1 + r ^ 2)⁻¹
  let F' : Real → Real := fun r => r * (1 + r ^ 2)⁻¹ ^ 2
  have hderiv : ∀ r ∈ Ici (0 : Real), HasDerivAt F (F' r) r := by
    intro r hr
    have hbase : HasDerivAt (fun s : Real => 1 + s ^ 2) (2 * r) r := by
      have hsum := (hasDerivAt_const (x := r) (c := (1 : Real))).add
        ((hasDerivAt_id r).mul (hasDerivAt_id r))
      have hfun : ((fun _ : Real => 1) + id * id) =
          (fun s : Real => 1 + s ^ 2) := by
        funext s
        simp only [Pi.add_apply, Pi.mul_apply, id_eq, pow_two]
      rw [hfun] at hsum
      simpa only [zero_add, one_mul, mul_one, id_eq, two_mul] using hsum
    have hne : 1 + r ^ 2 ≠ 0 := by positivity
    have hinv := hbase.inv hne
    have hmul := hinv.const_mul (-(1 / 2 : Real))
    have hmul' : HasDerivAt
        (fun s : Real => -(1 / 2) * (1 + s ^ 2)⁻¹)
        (-(1 / 2) * (-(2 * r) / (1 + r ^ 2) ^ 2)) r := hmul
    change HasDerivAt (fun s : Real => -(1 / 2) * (1 + s ^ 2)⁻¹)
      (r * (1 + r ^ 2)⁻¹ ^ 2) r
    convert hmul' using 1
    field_simp
  have hnonneg : ∀ r ∈ Ioi (0 : Real), 0 ≤ F' r := by
    intro r hr
    dsimp [F']
    exact mul_nonneg hr.le (sq_nonneg _)
  have hden : Tendsto (fun r : Real => 1 + r ^ 2) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by norm_num))
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hinv : Tendsto (fun r : Real => (1 + r ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    simpa [F] using hinv.const_mul (-(1 / 2 : Real))
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    hderiv hnonneg hlim
  simpa [F, F'] using hmain

theorem cauchyPeak_nonneg (z : Complex) : 0 ≤ cauchyPeak z := by
  dsimp [cauchyPeak]
  positivity

theorem integral_cauchyPeak : ∫ z : Complex, cauchyPeak z = 1 := by
  calc
    ∫ z : Complex, cauchyPeak z =
        ∫ p in polarCoord.target,
          p.1 * cauchyPeak (Complex.polarCoord.symm p) := by
      simpa [smul_eq_mul] using
        (Complex.integral_comp_polarCoord_symm cauchyPeak).symm
    _ = (∫ r in Ioi (0 : Real), r * (1 + r ^ 2)⁻¹ ^ 2) *
        ∫ _ in Ioo (-Real.pi) Real.pi, Real.pi⁻¹ := by
      change (∫ p in Ioi (0 : Real) ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 * cauchyPeak (Complex.polarCoord.symm p)) = _
      rw [← MeasureTheory.setIntegral_prod_mul,
        MeasureTheory.Measure.volume_eq_prod]
      refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
      intro p hp
      dsimp [cauchyPeak]
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
      field_simp [Real.pi_ne_zero]
    _ = 1 := by
      rw [integral_radial_cauchyPeak]
      rw [integral_const]
      have hvolume : MeasureTheory.volume.real (Ioo (-Real.pi) Real.pi) =
          2 * Real.pi := by
        rw [MeasureTheory.Measure.real, Real.volume_Ioo,
          ENNReal.toReal_ofReal]
        · ring
        · linarith [Real.pi_pos]
      simp only [MeasurableSet.univ, measureReal_restrict_apply,
        univ_inter, hvolume, smul_eq_mul]
      field_simp [Real.pi_ne_zero]

theorem cauchyPeak_decay :
    Tendsto (fun z : Complex => ‖z‖ ^ Module.finrank Real Complex * cauchyPeak z)
      (cobounded Complex) (𝓝 0) := by
  rw [Complex.finrank_real_complex]
  have hnorm : Tendsto (fun z : Complex => ‖z‖) (cobounded Complex) atTop :=
    tendsto_norm_cobounded_atTop
  have hscalar : Tendsto
      (fun r : Real => r ^ 2 * (Real.pi * (1 + r ^ 2) ^ 2)⁻¹)
      atTop (𝓝 0) := by
    have hzero : Tendsto (fun r : Real => (Real.pi * r ^ 2)⁻¹) atTop (𝓝 0) := by
      have hpow : Tendsto (fun r : Real => r ^ 2) atTop atTop :=
        tendsto_pow_atTop (by norm_num)
      have hmul : Tendsto (fun r : Real => Real.pi * r ^ 2) atTop atTop :=
        hpow.const_mul_atTop Real.pi_pos
      exact tendsto_inv_atTop_zero.comp hmul
    refine squeeze_zero' ?_ ?_ hzero
    · filter_upwards [eventually_gt_atTop (0 : Real)] with r hr
      positivity
    · filter_upwards [eventually_gt_atTop (0 : Real)] with r hr
      rw [inv_eq_one_div, inv_eq_one_div]
      rw [mul_one_div]
      change r ^ 2 / (Real.pi * (1 + r ^ 2) ^ 2) ≤
        1 / (Real.pi * r ^ 2)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc
        r ^ 2 * (Real.pi * r ^ 2) = Real.pi * (r ^ 2) ^ 2 := by ring
        _ ≤ Real.pi * (1 + r ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg r]) Real.pi_pos.le
        _ = 1 * (Real.pi * (1 + r ^ 2) ^ 2) := by ring
  apply (hscalar.comp hnorm).congr'
  exact Filter.Eventually.of_forall fun z => by
    simp only [Function.comp_apply, cauchyPeak]

theorem tendsto_integral_cauchyPeak_smul_of_integrable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [CompleteSpace V]
    {g : Complex → V} (hg : Integrable g) (hcont : ContinuousAt g 0) :
    Tendsto
      (fun c : Real => ∫ z : Complex,
        (c ^ 2 * cauchyPeak (c • z)) • g z)
      atTop (𝓝 (g 0)) := by
  simpa only [Complex.finrank_real_complex] using
    tendsto_integral_comp_smul_smul_of_integrable
      cauchyPeak_nonneg integral_cauchyPeak cauchyPeak_decay hg hcont

theorem tendsto_integral_regularized_quadratic_kernel_mul_of_integrable
    {a : Real} (ha : a ≠ 0) {g : Complex → Real}
    (hg : Integrable g) (hcont : ContinuousAt g 0) :
    Tendsto
      (fun c : Real => ∫ z : Complex,
        (a ^ 2 / c ^ 2) * g z *
          (a ^ 2 * ‖z‖ ^ 2 + a ^ 2 / c ^ 2)⁻¹ ^ 2)
      atTop (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  have hbase := tendsto_integral_cauchyPeak_smul_of_integrable hg hcont
  have hscaled := hbase.const_mul (Real.pi / a ^ 2)
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with c hc
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [smul_eq_mul]
  rw [cauchyPeak]
  rw [norm_smul]
  simp only [Real.norm_eq_abs, abs_of_pos hc]
  field_simp [ha, ne_of_gt hc, Real.pi_ne_zero]
  ring

end DifferentialGeometry.Analysis.Integration
