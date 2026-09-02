import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

noncomputable section

open Bornology Complex Filter MeasureTheory Real Set
open scoped Topology

namespace DifferentialGeometry.Analysis.Integration

theorem tendsto_integral_regularized_inv_sq_smul_of_integrable_of_ae_lower_bound
    {α V : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup V] [NormedSpace Real V]
    {u : α → Real} {b : α → V} {δ : Real}
    (hu : AEMeasurable u μ) (hb : Integrable b μ)
    (hδ : 0 < δ) (huδ : ∀ᵐ x ∂μ, δ ≤ u x) :
    Tendsto
      (fun ε : Real => ∫ x, (ε * (u x + ε)⁻¹ ^ 2) • b x ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  let F : Real → α → V := fun ε x => (ε * (u x + ε)⁻¹ ^ 2) • b x
  have hF_meas : ∀ ε : Real, AEStronglyMeasurable (F ε) μ := by
    intro ε
    exact (((hu.add_const ε).inv.pow_const 2).const_mul ε).aestronglyMeasurable.smul
      hb.aestronglyMeasurable
  have hbound_integrable : Integrable (fun x => δ⁻¹ * ‖b x‖) μ := by
    simpa only [smul_eq_mul] using hb.norm.const_mul δ⁻¹
  have hbound : ∀ᶠ ε : Real in 𝓝[>] 0,
      ∀ᵐ x ∂μ, ‖F ε x‖ ≤ δ⁻¹ * ‖b x‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    filter_upwards [huδ] with x hx
    have hu_pos : 0 < u x := hδ.trans_le hx
    have hden_pos : 0 < u x + ε := add_pos hu_pos hε
    have hscalar_nonneg : 0 ≤ ε * (u x + ε)⁻¹ ^ 2 :=
      mul_nonneg hε.le (sq_nonneg _)
    have hscalar_le : ε * (u x + ε)⁻¹ ^ 2 ≤ δ⁻¹ := by
      calc
        ε * (u x + ε)⁻¹ ^ 2 ≤ (u x + ε) * (u x + ε)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hu_pos.le) (sq_nonneg _)
        _ = (u x + ε)⁻¹ := by field_simp
        _ ≤ δ⁻¹ := (inv_le_inv₀ hden_pos hδ).2
          (hx.trans (le_add_of_nonneg_right hε.le))
    calc
      ‖F ε x‖ = (ε * (u x + ε)⁻¹ ^ 2) * ‖b x‖ := by
        change ‖(ε * (u x + ε)⁻¹ ^ 2) • b x‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscalar_nonneg]
      _ ≤ δ⁻¹ * ‖b x‖ :=
        mul_le_mul_of_nonneg_right hscalar_le (norm_nonneg _)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun ε => F ε x) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [huδ] with x hx
    have hu_ne : u x ≠ 0 := ne_of_gt (hδ.trans_le hx)
    have hε : Tendsto (fun ε : Real => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hden : Tendsto (fun ε : Real => u x + ε) (𝓝[>] 0) (𝓝 (u x)) :=
      by simpa only [add_zero] using tendsto_const_nhds.add hε
    have hscalar : Tendsto (fun ε : Real => ε * (u x + ε)⁻¹ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [zero_mul] using hε.mul ((hden.inv₀ hu_ne).pow 2)
    simpa only [F, zero_smul] using hscalar.smul_const (b x)
  simpa only [F, integral_zero] using
    tendsto_integral_filter_of_dominated_convergence
      (fun x => δ⁻¹ * ‖b x‖)
      (Filter.Eventually.of_forall hF_meas) hbound hbound_integrable hlim

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

theorem tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero
    {a : Real} (ha : a ≠ 0) {g : Complex → Real}
    (hg : Integrable g) (hcont : ContinuousAt g 0) :
    Tendsto
      (fun ε : Real => ∫ z : Complex,
        ε * g z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2)
      (𝓝[>] 0) (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  let c : Real → Real := fun ε => |a| * (Real.sqrt ε)⁻¹
  have hsqrt_full : Tendsto (fun ε : Real => Real.sqrt ε) (𝓝 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using Real.continuous_sqrt.tendsto (0 : Real)
  have hsqrt : Tendsto (fun ε : Real => Real.sqrt ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hsqrt_full.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Real.sqrt_pos.2 hε
  have hc : Tendsto c (𝓝[>] 0) atTop := by
    exact (tendsto_inv_nhdsGT_zero.comp hsqrt).const_mul_atTop (abs_pos.2 ha)
  have hbase :=
    (tendsto_integral_regularized_quadratic_kernel_mul_of_integrable ha hg hcont).comp hc
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  apply integral_congr_ae
  filter_upwards with z
  have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hscale : a ^ 2 / c ε ^ 2 = ε := by
    dsimp [c]
    field_simp [ha, ne_of_gt hsqrt_pos]
    rw [sq_abs, Real.sq_sqrt hε.le]
  rw [hscale]

theorem tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero
    {a : Real} (ha : a ≠ 0) {s : Set Complex}
    (hs : MeasurableSet s) (h0 : s ∈ 𝓝 (0 : Complex))
    {g : Complex → Real} (hg : IntegrableOn g s) (hcont : ContinuousAt g 0) :
    Tendsto
      (fun ε : Real => ∫ z in s,
        ε * g z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2)
      (𝓝[>] 0) (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  have h0s : (0 : Complex) ∈ s := mem_of_mem_nhds h0
  have hindicator : s.indicator g =ᶠ[𝓝 (0 : Complex)] g := by
    filter_upwards [h0] with z hz
    rw [indicator_of_mem hz]
  have hbase :=
    tendsto_integral_regularized_quadratic_kernel_mul_of_integrable_nhdsGT_zero
      ha (hg.integrable_indicator hs) (hcont.congr_of_eventuallyEq hindicator)
  rw [indicator_of_mem h0s] at hbase
  apply hbase.congr'
  filter_upwards with ε
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ s
  · simp only [indicator_of_mem hz]
  · simp only [indicator_of_notMem hz, mul_zero, zero_mul]

theorem tendsto_setIntegral_regularized_quadratic_kernel_comp_mul_abs_det_fderiv_of_integrableOn_nhdsGT_zero
    {a : Real} (ha : a ≠ 0) {s : Set Complex} (hs : MeasurableSet s)
    {φ : Complex → Complex} {φ' : Complex → Complex →L[Real] Complex}
    (hφ' : ∀ z ∈ s, HasFDerivWithinAt φ (φ' z) s z)
    (hφ : InjOn φ s) (h0 : φ '' s ∈ 𝓝 (0 : Complex))
    {g : Complex → Real} (hg : IntegrableOn g (φ '' s))
    (hcont : ContinuousAt g 0) :
    Tendsto
      (fun ε : Real => ∫ z in s,
        |(φ' z).det| *
          (ε * g (φ z) * (a ^ 2 * ‖φ z‖ ^ 2 + ε)⁻¹ ^ 2))
      (𝓝[>] 0) (𝓝 (Real.pi / a ^ 2 * g 0)) := by
  have himage : MeasurableSet (φ '' s) :=
    measurable_image_of_fderivWithin hs hφ' hφ
  have hbase :=
    tendsto_setIntegral_regularized_quadratic_kernel_mul_of_integrableOn_nhdsGT_zero
      ha himage h0 hg hcont
  apply hbase.congr'
  filter_upwards with ε
  simpa only [smul_eq_mul] using
    (integral_image_eq_integral_abs_det_fderiv_smul volume hs hφ' hφ
      (fun z : Complex =>
        ε * g z * (a ^ 2 * ‖z‖ ^ 2 + ε)⁻¹ ^ 2))

end DifferentialGeometry.Analysis.Integration
