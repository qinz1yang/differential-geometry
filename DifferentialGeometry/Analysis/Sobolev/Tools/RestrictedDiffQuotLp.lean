import DifferentialGeometry.Analysis.Sobolev.Tools.CutoffDiffQuotLp

noncomputable section

open Filter MeasureTheory Set Metric
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem indicator_one_memLp_top {K : Set E} (hK : MeasurableSet K) :
    MemLp (K.indicator (fun _ => (1 : ℝ))) ∞ volume := by
  apply memLp_top_of_bound (measurable_const.indicator hK).aestronglyMeasurable 1
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ K <;> simp [hx]

private theorem tsupport_indicator_one_subset (K : Set E) :
    tsupport (K.indicator (fun _ => (1 : ℝ))) ⊆ closure K := by
  apply closure_mono
  intro x hx
  by_contra hxK
  exact hx (indicator_of_notMem hxK _)

theorem integrable_integral_sq_diffQuot_on_comp
    {Z Y : Type*} [MeasurableSpace Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {μ : Measure Z} {Ω K : Set E} (hΩ : MeasurableSet Ω) (hK : MeasurableSet K)
    (k : Fin d) (h : ℝ) (hroom : cthickening |h| K ⊆ Ω)
    (A : Y →L[ℝ] Lp ℝ 2 (volume.restrict Ω)) {u : Z → Y} (hu : MemLp u 2 μ) :
    Integrable (fun t => ∫ x in K, (diffQuot k h (A (u t)) x)^2) μ := by
  let χ := K.indicator (fun _ => (1 : ℝ))
  have hχ : MemLp χ ∞ volume := indicator_one_memLp_top hK
  have hχroom : cthickening |h| (tsupport χ) ⊆ Ω :=
    (cthickening_subset_of_subset |h| (tsupport_indicator_one_subset K)).trans
      (by simpa only [cthickening_closure] using hroom)
  have hint := integrable_integral_sq_cutoff_diffQuot_comp hΩ hχ k h hχroom A hu
  apply hint.congr
  filter_upwards [] with t
  rw [← integral_indicator hK]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ K <;> simp [χ, hx]

theorem diffQuot_congr_ae_on
    {Ω K : Set E} (hΩ : MeasurableSet Ω) (hK : MeasurableSet K)
    (k : Fin d) (h : ℝ) (hroom : cthickening |h| K ⊆ Ω)
    {u v : E → ℝ} (huv : u =ᵐ[volume.restrict Ω] v) :
    diffQuot k h u =ᵐ[volume.restrict K] diffQuot k h v := by
  let χ := K.indicator (fun _ => (1 : ℝ))
  have hχroom : cthickening |h| (tsupport χ) ⊆ Ω :=
    (cthickening_subset_of_subset |h| (tsupport_indicator_one_subset K)).trans
      (by simpa only [cthickening_closure] using hroom)
  have heq : (fun x => χ x * diffQuot k h u x) =ᵐ[volume.restrict K]
      fun x => χ x * diffQuot k h v x :=
    (cutoff_diffQuot_congr_ae_local hΩ k h χ hχroom huv).filter_mono
      (ae_mono Measure.restrict_le_self)
  filter_upwards [heq, ae_restrict_mem hK] with x hx hxK
  simpa only [χ, indicator_of_mem hxK, one_mul] using hx

end DifferentialGeometry.Analysis.Sobolev
