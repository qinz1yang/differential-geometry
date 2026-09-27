import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientBounds
import DifferentialGeometry.Analysis.Integration.LpNorm
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} [SFinite μ]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "ν" => μ.prod (volume : Measure E)

private local instance : MeasurableSpace E := WithLp.measurableSpace 2 (Fin d → ℝ)

private theorem memLp_spatial_diffQuot {w : Z × E → ℝ} (hw : MemLp w 2 ν)
    (k : Fin d) (h : ℝ) :
    MemLp (fun p : Z × E => diffQuot k h (fun x => w (p.1, x)) p.2) 2 ν := by
  by_cases hh : h = 0
  · simp only [hh, diffQuot_zero_h, Pi.zero_apply]
    exact MemLp.zero
  have ht := hw.comp_measurePreserving ((MeasurePreserving.id μ).prod
    (measurePreserving_add_right volume (h • EuclideanSpace.single k (1 : ℝ))))
  have hb := (ht.sub hw).const_smul h⁻¹
  convert hb using 1
  funext p
  rw [diffQuot_apply_of_ne k hh]
  change (w (p.1, p.2 + h • EuclideanSpace.single k 1) - w p) / h =
    h⁻¹ * (w (p.1, p.2 + h • EuclideanSpace.single k 1) - w p)
  ring

omit [SFinite μ] in
private theorem memLp_spatial_mul_cutoff {w : Z × E → ℝ} (hw : MemLp w 2 ν)
    {η : E → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η) :
    MemLp (fun p : Z × E => η p.2 * w p) 2 ν := by
  obtain ⟨A, hA⟩ := hηc.exists_bound_of_continuous hη
  apply hw.of_le_mul (c := A) ((hη.stronglyMeasurable.comp_measurable measurable_snd).aestronglyMeasurable.mul
    hw.aestronglyMeasurable)
  exact Eventually.of_forall fun p => by
    change ‖η p.2 * w p‖ ≤ A * ‖w p‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA p.2) (norm_nonneg _)

theorem eLpNorm_spatial_diffQuot_cutoff_mul_le
    {w : Z × E → ℝ} (hw : MemLp w 2 ν)
    {η : E → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) {L : ℝ} (hL : ∀ x, |diffQuot k h η x| ≤ L) :
    eLpNorm (fun p : Z × E => diffQuot k h (fun x => η x * w (p.1, x)) p.2) 2 ν ≤
      eLpNorm (fun p : Z × E => η p.2 * diffQuot k h (fun x => w (p.1, x)) p.2) 2 ν +
        ENNReal.ofReal L * eLpNorm w 2 ν := by
  let f : Z × E → ℝ := fun p => η p.2 * diffQuot k h (fun x => w (p.1, x)) p.2
  let g : Z × E → ℝ := fun p => diffQuot k h η p.2 * w (p.1, p.2 + h • EuclideanSpace.single k 1)
  have hf : MemLp f 2 ν := memLp_spatial_mul_cutoff (memLp_spatial_diffQuot hw k h) hη hηc
  have htrans := (MeasurePreserving.id μ).prod
    (measurePreserving_add_right volume (h • EuclideanSpace.single k (1 : ℝ)))
  have ht : MemLp (fun p : Z × E => w (p.1, p.2 + h • EuclideanSpace.single k 1)) 2 ν :=
    hw.comp_measurePreserving htrans
  have hgm : AEStronglyMeasurable g ν :=
    (((continuous_diffQuot_of_continuous k h hη).stronglyMeasurable.comp_measurable
      measurable_snd).aestronglyMeasurable).mul ht.aestronglyMeasurable
  have hgb : ∀ᵐ p ∂ν, ‖g p‖ ≤ L * ‖w (p.1, p.2 + h • EuclideanSpace.single k 1)‖ :=
    Eventually.of_forall fun p => by
      dsimp only [g]
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hL p.2) (norm_nonneg _)
  have hg : MemLp g 2 ν := ht.of_le_mul hgm hgb
  have heq : (fun p : Z × E => diffQuot k h (fun x => η x * w (p.1, x)) p.2) = f + g := by
    funext p
    by_cases hh : h = 0
    · simp only [hh, diffQuot_zero_h, Pi.zero_apply, f, g, mul_zero, zero_mul, Pi.add_apply, add_zero]
    · simp only [diffQuot_apply_of_ne k hh, Pi.add_apply, f, g]
      ring
  rw [heq]
  calc
    _ ≤ eLpNorm f 2 ν + eLpNorm g 2 ν := eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable (by norm_num)
    _ ≤ eLpNorm f 2 ν + ENNReal.ofReal L *
        eLpNorm (fun p : Z × E => w (p.1, p.2 + h • EuclideanSpace.single k 1)) 2 ν :=
      add_le_add_right (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hgb 2) _
    _ = _ := by
      have he := eLpNorm_comp_measurePreserving (p := 2) hw.aestronglyMeasurable htrans
      exact congrArg (fun z => eLpNorm f 2 ν + ENNReal.ofReal L * z) he

theorem exists_uniform_eLpNorm_spatial_diffQuot_cutoff_mul_le
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {w : Z × E → ℝ}, MemLp w 2 ν →
      ∀ (k : Fin d) (h : ℝ),
      eLpNorm (fun p : Z × E => diffQuot k h (fun x => η x * w (p.1, x)) p.2) 2 ν ≤
        eLpNorm (fun p : Z × E => η p.2 * diffQuot k h (fun x => w (p.1, x)) p.2) 2 ν +
          ENNReal.ofReal L * eLpNorm w 2 ν := by
  obtain ⟨L, hL⟩ := (hηc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous (hη.continuous_fderiv (by norm_num))
  have hL0 : 0 ≤ L := (norm_nonneg (fderiv ℝ η 0)).trans (hL 0)
  refine ⟨L, hL0, ?_⟩
  intro w hw k h
  apply eLpNorm_spatial_diffQuot_cutoff_mul_le hw hη.continuous hηc k h
  intro x
  exact abs_diffQuot_le_of_norm_fderiv_le (fun y _ => hη.differentiable_one y)
    (fun y _ => hL y) k h (subset_univ _)

theorem exists_uniform_integral_sq_spatial_diffQuot_cutoff_mul_le
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {w : Z × E → ℝ} (hw : MemLp w 2 ν)
      (k : Fin d) (h : ℝ),
      (∫ t, ∫ x, (diffQuot k h (fun y => η y * w (t, y)) x)^2 ∂volume ∂μ) ≤
        2 * (∫ t, ∫ x, (η x * diffQuot k h (fun y => w (t, y)) x)^2 ∂volume ∂μ) +
          L * ‖hw.toLp w‖^2 := by
  obtain ⟨L, hL, hbound⟩ := exists_uniform_eLpNorm_spatial_diffQuot_cutoff_mul_le
    (μ := μ) hη hηc
  refine ⟨2 * L^2, by positivity, ?_⟩
  intro w hw k h
  let f : Z × E → ℝ := fun p => diffQuot k h (fun x => η x * w (p.1, x)) p.2
  let g : Z × E → ℝ := fun p => η p.2 * diffQuot k h (fun x => w (p.1, x)) p.2
  have hf : MemLp f 2 ν := memLp_spatial_diffQuot (memLp_spatial_mul_cutoff hw hη.continuous hηc) k h
  have hg : MemLp g 2 ν := memLp_spatial_mul_cutoff (memLp_spatial_diffQuot hw k h) hη.continuous hηc
  have hb : (eLpNorm f 2 ν).toReal ≤ (eLpNorm g 2 ν).toReal + L * (eLpNorm w 2 ν).toReal := by
    have hnorm := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨hg.eLpNorm_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw.eLpNorm_ne_top⟩)
        (hbound hw k h)
    rw [ENNReal.toReal_add hg.eLpNorm_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw.eLpNorm_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hL] at hnorm
    exact hnorm
  have hs : (eLpNorm f 2 ν).toReal^2 ≤
      2 * (eLpNorm g 2 ν).toReal^2 + 2 * L^2 * (eLpNorm w 2 ν).toReal^2 := by
    have hs := pow_le_pow_left₀ ENNReal.toReal_nonneg hb 2
    nlinarith [sq_nonneg ((eLpNorm g 2 ν).toReal - L * (eLpNorm w 2 ν).toReal)]
  rw [← Analysis.Integration.integral_sq_eq_l2 hf, ← Analysis.Integration.integral_sq_eq_l2 hg] at hs
  rw [integral_prod _ hf.integrable_sq, integral_prod _ hg.integrable_sq] at hs
  simpa only [Lp.norm_toLp] using hs

theorem exists_cutoff_toLp_spatial_diffQuot_uniform_bound
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {w : Z × E → ℝ}, MemLp w 2 ν →
      ∀ (k : Fin d) {C r : ℝ}, 0 ≤ C →
      (∀ h : ℝ, 0 < |h| → |h| ≤ r →
        eLpNorm (fun p : Z × E => η p.2 * diffQuot k h (fun x => w (p.1, x)) p.2)
          2 ν ≤ ENNReal.ofReal C) →
      ∃ u : Lp ℝ 2 ν, (u : Z × E → ℝ) =ᵐ[ν] (fun p => η p.2 * w p) ∧
        ∀ h : ℝ, 0 < |h| → |h| ≤ r →
        eLpNorm (fun p : Z × E => diffQuot k h (fun x => u (p.1, x)) p.2) 2 ν ≤
          ENNReal.ofReal (C + L * (eLpNorm w 2 ν).toReal) := by
  obtain ⟨L, hL, hbound⟩ := exists_uniform_eLpNorm_spatial_diffQuot_cutoff_mul_le
    (μ := μ) hη hηc
  refine ⟨L, hL, ?_⟩
  intro w hw k C r hC hlocal
  have hcut := memLp_spatial_mul_cutoff hw hη.continuous hηc
  let u : Lp ℝ 2 ν := hcut.toLp (fun p => η p.2 * w p)
  have hueq : (u : Z × E → ℝ) =ᵐ[ν] fun p => η p.2 * w p := hcut.coeFn_toLp
  refine ⟨u, hueq, ?_⟩
  intro h hh hhr
  have htrans := (MeasurePreserving.id μ).prod
    (measurePreserving_add_right volume (h • EuclideanSpace.single k (1 : ℝ)))
  have hdq : (fun p : Z × E => diffQuot k h (fun x => u (p.1, x)) p.2) =ᵐ[ν]
      fun p : Z × E => diffQuot k h (fun x => η x * w (p.1, x)) p.2 := by
    have hshift := htrans.quasiMeasurePreserving.ae_eq hueq
    filter_upwards [hueq, hshift] with p hp hps
    have hp' : u (p.1, p.2) = η p.2 * w (p.1, p.2) := hp
    have hps' : u (p.1, p.2 + h • EuclideanSpace.single k 1) =
        η (p.2 + h • EuclideanSpace.single k 1) * w (p.1, p.2 + h • EuclideanSpace.single k 1) := hps
    simp only [diffQuot_apply_of_ne k (abs_pos.mp hh), hp', hps']
  rw [eLpNorm_congr_ae hdq]
  calc
    _ ≤ eLpNorm (fun p : Z × E => η p.2 * diffQuot k h (fun x => w (p.1, x)) p.2) 2 ν +
        ENNReal.ofReal L * eLpNorm w 2 ν := hbound hw k h
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal L * eLpNorm w 2 ν :=
      add_le_add_left (hlocal h hh hhr) _
    _ = _ := by
      rw [ENNReal.ofReal_add hC (mul_nonneg hL ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul hL, ENNReal.ofReal_toReal hw.eLpNorm_ne_top]

theorem exists_cutoff_toLp_spatial_diffQuot_uniform_bound_of_integral_sq
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {w : Z × E → ℝ}, MemLp w 2 ν →
      ∀ (k : Fin d) {C r : ℝ},
      (∀ h : ℝ, 0 < |h| → |h| ≤ r →
        (∫ t, ∫ x, (η x * diffQuot k h (fun y => w (t, y)) x)^2 ∂volume ∂μ) ≤ C) →
      ∃ u : Lp ℝ 2 ν, (u : Z × E → ℝ) =ᵐ[ν] (fun p => η p.2 * w p) ∧
        ∀ h : ℝ, 0 < |h| → |h| ≤ r →
        eLpNorm (fun p : Z × E => diffQuot k h (fun x => u (p.1, x)) p.2) 2 ν ≤
          ENNReal.ofReal (Real.sqrt C + L * (eLpNorm w 2 ν).toReal) := by
  obtain ⟨L, hL, hbound⟩ := exists_cutoff_toLp_spatial_diffQuot_uniform_bound (μ := μ) hη hηc
  refine ⟨L, hL, ?_⟩
  intro w hw k C r hlocal
  apply hbound hw k (Real.sqrt_nonneg C)
  intro h hh hr
  let f : Z × E → ℝ := fun p => η p.2 * diffQuot k h (fun x => w (p.1, x)) p.2
  have hf : MemLp f 2 ν := memLp_spatial_mul_cutoff (memLp_spatial_diffQuot hw k h) hη.continuous hηc
  have hs : (eLpNorm f 2 ν).toReal^2 ≤ C := by
    rw [← Analysis.Integration.integral_sq_eq_l2 hf, integral_prod _ hf.integrable_sq]
    exact hlocal h hh hr
  have hsqrt := Real.le_sqrt_of_sq_le hs
  calc
    _ = ENNReal.ofReal (eLpNorm f 2 ν).toReal := (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm
    _ ≤ ENNReal.ofReal (Real.sqrt C) := ENNReal.ofReal_le_ofReal hsqrt

omit [MeasurableSpace Z] in
private theorem spatial_indicator_eq_indicator_prod (Ω : Set E) (w : Z × E → ℝ) :
    (fun p : Z × E => Ω.indicator (fun x => w (p.1, x)) p.2) =
      (univ ×ˢ Ω).indicator w := by
  funext p
  by_cases hp : p.2 ∈ Ω
  · simp only [indicator_of_mem hp,
      indicator_of_mem (show p ∈ univ ×ˢ Ω from ⟨mem_univ _, hp⟩)]
  · simp only [indicator_of_notMem hp,
      indicator_of_notMem (show p ∉ univ ×ˢ Ω from fun h => hp h.2)]

private theorem memLp_spatial_indicator {Ω : Set E} (hΩ : MeasurableSet Ω)
    {w : Z × E → ℝ} (hw : MemLp w 2 (μ.prod (volume.restrict Ω))) :
    MemLp (fun p : Z × E => Ω.indicator (fun x => w (p.1, x)) p.2) 2 ν := by
  rw [spatial_indicator_eq_indicator_prod]
  apply (memLp_indicator_iff_restrict (MeasurableSet.univ.prod hΩ)).mpr
  simpa only [← Measure.prod_restrict, Measure.restrict_univ] using hw

private theorem eLpNorm_spatial_indicator {Ω : Set E} (hΩ : MeasurableSet Ω)
    (w : Z × E → ℝ) :
    eLpNorm (fun p : Z × E => Ω.indicator (fun x => w (p.1, x)) p.2) 2 ν =
      eLpNorm w 2 (μ.prod (volume.restrict Ω)) := by
  rw [spatial_indicator_eq_indicator_prod,
    eLpNorm_indicator_eq_eLpNorm_restrict (MeasurableSet.univ.prod hΩ),
    ← Measure.prod_restrict, Measure.restrict_univ]

private theorem cutoff_mul_diffQuot_indicator_eq {Ω : Set E} {η w : E → ℝ}
    (k : Fin d) (h : ℝ) (hroom : cthickening |h| (tsupport η) ⊆ Ω) (x : E) :
    η x * diffQuot k h (Ω.indicator w) x = η x * diffQuot k h w x := by
  by_cases hηx : η x = 0
  · simp only [hηx, zero_mul]
  have hx := subset_tsupport η hηx
  have hxΩ := hroom (self_subset_cthickening _ hx)
  have hsΩ : x + h • EuclideanSpace.single k (1 : ℝ) ∈ Ω := by
    apply hroom
    apply closedBall_subset_cthickening hx |h|
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]
  by_cases hh : h = 0
  · simp only [hh, diffQuot_zero_h, Pi.zero_apply]
  simp only [diffQuot_apply_of_ne k hh, indicator_of_mem hxΩ, indicator_of_mem hsΩ]

theorem exists_cutoff_toLp_spatial_diffQuot_uniform_bound_on
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {Ω : Set E}, MeasurableSet Ω →
      ∀ {w : Z × E → ℝ}, MemLp w 2 (μ.prod (volume.restrict Ω)) →
      ∀ (k : Fin d) {C r : ℝ}, cthickening r (tsupport η) ⊆ Ω →
      (∀ h : ℝ, 0 < |h| → |h| ≤ r →
        (∫ t, ∫ x, (η x * diffQuot k h (fun y => w (t, y)) x)^2 ∂volume ∂μ) ≤ C) →
      ∃ u : Lp ℝ 2 ν, (u : Z × E → ℝ) =ᵐ[ν] (fun p => η p.2 * w p) ∧
        ∀ h : ℝ, 0 < |h| → |h| ≤ r →
        eLpNorm (fun p : Z × E => diffQuot k h (fun x => u (p.1, x)) p.2) 2 ν ≤
          ENNReal.ofReal (Real.sqrt C + L * (eLpNorm w 2 (μ.prod (volume.restrict Ω))).toReal) := by
  obtain ⟨L, hL, hbound⟩ := exists_cutoff_toLp_spatial_diffQuot_uniform_bound_of_integral_sq
    (μ := μ) hη hηc
  refine ⟨L, hL, ?_⟩
  intro Ω hΩ w hw k C r hroom hlocal
  let W : Z × E → ℝ := fun p => Ω.indicator (fun x => w (p.1, x)) p.2
  have hW : MemLp W 2 ν := memLp_spatial_indicator hΩ hw
  have hηs : tsupport η ⊆ Ω := (self_subset_cthickening _).trans hroom
  have hcut : (fun p : Z × E => η p.2 * W p) = fun p => η p.2 * w p := by
    funext p
    by_cases hp : p.2 ∈ Ω
    · simp only [W, indicator_of_mem hp]
    · simp only [W, indicator_of_notMem hp, mul_zero,
        image_eq_zero_of_notMem_tsupport (fun h => hp (hηs h)), zero_mul]
  have hb : ∀ h : ℝ, 0 < |h| → |h| ≤ r →
      (∫ t, ∫ x, (η x * diffQuot k h (fun y => W (t, y)) x)^2 ∂volume ∂μ) ≤ C := by
    intro h hh hr
    have heq : (fun t => ∫ x, (η x * diffQuot k h (fun y => W (t, y)) x)^2) =
        fun t => ∫ x, (η x * diffQuot k h (fun y => w (t, y)) x)^2 := by
      funext t
      apply integral_congr_ae
      exact Eventually.of_forall fun x => congrArg (fun z : ℝ => z^2)
        (cutoff_mul_diffQuot_indicator_eq k h ((cthickening_mono hr _).trans hroom) x)
    rw [heq]
    exact hlocal h hh hr
  obtain ⟨u, hu, hub⟩ := hbound hW k hb
  refine ⟨u, ?_, ?_⟩
  · exact hu.trans (Eventually.of_forall fun p => congrFun hcut p)
  · intro h hh hr
    have hb := hub h hh hr
    simpa only [W, eLpNorm_spatial_indicator hΩ w] using hb

end DifferentialGeometry.Analysis.Sobolev
