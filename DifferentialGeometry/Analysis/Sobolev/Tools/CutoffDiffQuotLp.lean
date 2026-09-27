import DifferentialGeometry.Analysis.Integration.Lp.Product
import DifferentialGeometry.Analysis.Integration.Lp.ZeroExtension
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Sobolev
import Mathlib.MeasureTheory.Function.Holder

noncomputable section

open Filter MeasureTheory Set Metric
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

def cutoffDiffQuotLp {Ω : Set E} (hΩ : MeasurableSet Ω)
    {η : E → ℝ} (hη : MemLp η ∞ volume) (k : Fin d) (h : ℝ) :
    Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  let T := (Lp.compMeasurePreservingₗᵢ ℝ (fun x : E => x + h • EuclideanSpace.single k 1)
    (measurePreserving_add_right volume _)).toContinuousLinearMap
  let D := h⁻¹ • (T - ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume : Measure E)))
  ((ContinuousLinearMap.mul ℝ ℝ).holderL volume ∞ 2 2 (hη.toLp η)).comp
    (D.comp (Lp.zeroExtendₗᵢ (𝕜 := ℝ) hΩ).toContinuousLinearMap)

theorem cutoffDiffQuotLp_coeFn {Ω : Set E} (hΩ : MeasurableSet Ω)
    {η : E → ℝ} (hη : MemLp η ∞ volume) (k : Fin d) (h : ℝ)
    (hroom : cthickening |h| (tsupport η) ⊆ Ω) (u : Lp ℝ 2 (volume.restrict Ω)) :
    cutoffDiffQuotLp hΩ hη k h u =ᵐ[volume] fun x => η x * diffQuot k h u x := by
  let U := Lp.zeroExtend hΩ u
  let T := Lp.compMeasurePreserving (fun x : E => x + h • EuclideanSpace.single k 1)
    (measurePreserving_add_right volume _) U
  let Q := h⁻¹ • (T - U)
  have htranslate : T =ᵐ[volume] fun x => U (x + h • EuclideanSpace.single k 1) :=
    Lp.coeFn_compMeasurePreserving U (measurePreserving_add_right volume _)
  have hU := Lp.coeFn_zeroExtend hΩ u
  have hshift := (measurePreserving_add_right volume (h • EuclideanSpace.single k (1 : ℝ))).quasiMeasurePreserving.ae hU
  have hQ : Q =ᵐ[volume] fun x => h⁻¹ * (Ω.indicator u (x + h • EuclideanSpace.single k 1) - Ω.indicator u x) := by
    filter_upwards [Lp.coeFn_smul h⁻¹ (T - U), Lp.coeFn_sub T U, htranslate, hU, hshift]
      with x hs hsub ht hu hh
    rw [hs, Pi.smul_apply, hsub, Pi.sub_apply, ht, hu, hh, smul_eq_mul]
  have hholder := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (hη.toLp η) Q
  change (cutoffDiffQuotLp hΩ hη k h u) =ᵐ[volume] _
  filter_upwards [hholder, hQ, hη.coeFn_toLp] with x hm hq hηx
  change (ContinuousLinearMap.mul ℝ ℝ).holder 2 (hη.toLp η) Q x = _
  rw [hm, ContinuousLinearMap.mul_apply', hηx, hq]
  by_cases hh : h = 0
  · simp [hh]
  by_cases hx : η x = 0
  · simp only [hx, zero_mul]
  have hxs : x ∈ tsupport η := subset_tsupport η hx
  have hxΩ : x ∈ Ω := hroom (self_subset_cthickening _ hxs)
  have hsΩ : x + h • EuclideanSpace.single k (1 : ℝ) ∈ Ω := by
    apply hroom
    apply closedBall_subset_cthickening hxs |h|
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]
  rw [indicator_of_mem hxΩ, indicator_of_mem hsΩ, diffQuot_apply_of_ne k hh]
  ring


theorem integral_sq_cutoffDiffQuotLp {Ω : Set E} (hΩ : MeasurableSet Ω)
    {η : E → ℝ} (hη : MemLp η ∞ volume) (k : Fin d) (h : ℝ)
    (hroom : cthickening |h| (tsupport η) ⊆ Ω) (u : Lp ℝ 2 (volume.restrict Ω)) :
    (∫ x, (η x * diffQuot k h u x) ^ 2) = ‖cutoffDiffQuotLp hΩ hη k h u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cutoffDiffQuotLp_coeFn hΩ hη k h hroom u] with x hx
  simp only [Real.inner_apply, hx, pow_two]

theorem integrable_integral_sq_cutoff_diffQuot_comp
    {Z Y : Type*} [MeasurableSpace Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {μ : Measure Z} {Ω : Set E} (hΩ : MeasurableSet Ω)
    {η : E → ℝ} (hη : MemLp η ∞ volume) (k : Fin d) (h : ℝ)
    (hroom : cthickening |h| (tsupport η) ⊆ Ω)
    (A : Y →L[ℝ] Lp ℝ 2 (volume.restrict Ω)) {u : Z → Y} (hu : MemLp u 2 μ) :
    Integrable (fun t => ∫ x, (η x * diffQuot k h (A (u t)) x) ^ 2) μ := by
  let hc := (cutoffDiffQuotLp hΩ hη k h).comp A
  have hmem := hu.continuousLinearMap_comp hc
  have hi := hmem.norm.integrable_sq
  apply hi.congr
  filter_upwards [] with t
  change ‖cutoffDiffQuotLp hΩ hη k h (A (u t))‖ ^ 2 = _
  exact (integral_sq_cutoffDiffQuotLp hΩ hη k h hroom (A (u t))).symm


theorem cutoff_diffQuot_congr_ae_local {Ω : Set E} (hΩ : MeasurableSet Ω)
    (k : Fin d) (h : ℝ) (η : E → ℝ)
    (hroom : cthickening |h| (tsupport η) ⊆ Ω) {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v) :
    (fun x => η x * diffQuot k h u x) =ᵐ[volume] fun x => η x * diffQuot k h v x := by
  have hind : Ω.indicator u =ᵐ[volume] Ω.indicator v := by
    rw [EventuallyEq, ae_restrict_iff' hΩ] at huv
    filter_upwards [huv] with x hx
    by_cases hxΩ : x ∈ Ω
    · simp only [indicator_of_mem hxΩ, hx hxΩ]
    · simp only [indicator_of_notMem hxΩ]
  have hs := (measurePreserving_add_right volume
    (h • EuclideanSpace.single k (1 : ℝ))).quasiMeasurePreserving.ae_eq hind
  filter_upwards [hind, hs] with x hx hsx
  by_cases hηx : η x = 0
  · simp only [hηx, zero_mul]
  have hxs : x ∈ tsupport η := subset_tsupport η hηx
  have hxΩ : x ∈ Ω := hroom (self_subset_cthickening _ hxs)
  have hsΩ : x + h • EuclideanSpace.single k (1 : ℝ) ∈ Ω := by
    apply hroom
    apply closedBall_subset_cthickening hxs |h|
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]
  simp only [indicator_of_mem hxΩ] at hx
  change Ω.indicator u (x + h • EuclideanSpace.single k 1) =
    Ω.indicator v (x + h • EuclideanSpace.single k 1) at hsx
  simp only [indicator_of_mem hsΩ] at hsx
  simp only [diffQuot, hx, hsx]

theorem integral_sq_cutoff_diffQuot_uncurry_compLpL
    {Z Y : Type*} [MeasurableSpace Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {μ : Measure Z} {Ω : Set E} (hΩ : MeasurableSet Ω)
    (A : Y →L[ℝ] Lp ℝ 2 (volume.restrict Ω)) (u : Lp Y 2 μ)
    (η : E → ℝ) (k : Fin d) (h : ℝ)
    (hroom : cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ t, (∫ x, (η x * diffQuot k h
      (fun y => Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (A.compLpL 2 μ u) (t, y)) x)^2) ∂μ) =
      ∫ t, (∫ x, (η x * diffQuot k h (A (u t)) x)^2) ∂μ := by
  apply integral_congr_ae
  filter_upwards [Lp.uncurry_compLpL_coeFn (𝕜 := ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) A u]
    with t ht
  exact integral_congr_ae ((cutoff_diffQuot_congr_ae_local hΩ k h η hroom ht).fun_comp (· ^ 2))

end DifferentialGeometry.Analysis.Sobolev
