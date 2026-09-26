import DifferentialGeometry.Analysis.Integration.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
open Filter
open scoped Topology

namespace intervalIntegral

open MeasureTheory Set

private theorem tendsto_integral_one_sub_sq_div_sq_mul_zero_left
    {H : ℝ → ℝ} {v : ℝ} (hv : 0 < v)
    (hH : IntervalIntegrable H volume 0 v) :
    Tendsto (fun a : ℝ => ∫ r in a..v, (1 - a ^ 2 / r ^ 2) * H r)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in (0 : ℝ)..v, H r)) := by
  let μ := volume.restrict (Ioc (0 : ℝ) v)
  let F : ℝ → ℝ → ℝ := fun a => (Ioi a).indicator
    (fun r => (1 - a ^ 2 / r ^ 2) * H r)
  have hHi : Integrable H μ := (intervalIntegrable_iff_integrableOn_Ioc_of_le hv.le).mp hH
  have hmeas (a : ℝ) : AEStronglyMeasurable (F a) μ := by
    exact ((measurable_const.sub (measurable_const.div (measurable_id.pow_const 2))).aestronglyMeasurable.mul hHi.aestronglyMeasurable).indicator measurableSet_Ioi
  have hbound : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ᵐ r ∂μ, ‖F a r‖ ≤ ‖H r‖ := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    by_cases har : a < r
    · have ha' : 0 < a := ha
      have hquot : 0 ≤ a ^ 2 / r ^ 2 := div_nonneg (sq_nonneg a) (sq_nonneg r)
      have hquot1 : a ^ 2 / r ^ 2 ≤ 1 :=
        (div_le_one (sq_pos_of_pos hr.1)).mpr ((sq_le_sq₀ ha'.le hr.1.le).mpr har.le)
      simp only [F, Set.indicator_of_mem (show r ∈ Ioi a from har), norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hquot1)]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith : 1 - a ^ 2 / r ^ 2 ≤ 1)
    · simp only [F, Set.indicator_of_notMem (show r ∉ Ioi a from har), norm_zero]
      exact norm_nonneg _
  have hlim : ∀ᵐ r ∂μ, Tendsto (fun a => F a r) (𝓝[>] (0 : ℝ)) (𝓝 (H r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hevent : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < r :=
      (eventually_lt_nhds hr.1).filter_mono nhdsWithin_le_nhds
    have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hbase : Tendsto (fun a : ℝ => (1 - a ^ 2 / r ^ 2) * H r)
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 - (0 : ℝ) ^ 2 / r ^ 2) * H r)) :=
      (tendsto_const_nhds.sub ((hid.pow 2).div_const (r ^ 2))).mul_const (H r)
    have hbase' : Tendsto (fun a : ℝ => (1 - a ^ 2 / r ^ 2) * H r)
        (𝓝[>] (0 : ℝ)) (𝓝 (H r)) := by
      simpa only [zero_pow two_ne_zero, zero_div, sub_zero, one_mul] using hbase
    apply hbase'.congr'
    filter_upwards [hevent] with a ha
    simp only [F, Set.indicator_of_mem (show r ∈ Ioi a from ha)]
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun r => ‖H r‖) (Eventually.of_forall hmeas) hbound hHi.norm hlim
  rw [← intervalIntegral.integral_of_le hv.le] at hmain
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hv).filter_mono nhdsWithin_le_nhds] with a ha hav
  change (∫ r, F a r ∂μ) = _
  dsimp only [F]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  change (∫ r, (1 - a ^ 2 / r ^ 2) * H r ∂(volume.restrict (Ioc 0 v)).restrict (Ioi a)) = _
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi a ∩ Ioc (0 : ℝ) v = Ioc a v := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, ha.trans h.1, h.2⟩
  rw [hset, intervalIntegral.integral_of_le hav.le]

theorem tendsto_integral_one_sub_sq_div_sq_mul
    {L : ℝ → ℝ} {l v : ℝ} (hl : 0 ≤ l) (hlv : l < v)
    (hL : IntervalIntegrable L volume l v) :
    Tendsto (fun a : ℝ => ∫ r in max a l..v, (1 - a ^ 2 / r ^ 2) * L r)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in l..v, L r)) := by
  let G : ℝ → ℝ := (Ioc l v).indicator L
  have hv : 0 < v := hl.trans_lt hlv
  have hset : Ioc l v ∩ Ioc (0 : ℝ) v = Ioc l v :=
    inter_eq_left.mpr (Ioc_subset_Ioc hl le_rfl)
  have hG : IntervalIntegrable G volume 0 v := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hv.le]
    change Integrable ((Ioc l v).indicator L) (volume.restrict (Ioc 0 v))
    rw [integrable_indicator_iff measurableSet_Ioc]
    change Integrable L ((volume.restrict (Ioc 0 v)).restrict (Ioc l v))
    rw [Measure.restrict_restrict measurableSet_Ioc, hset]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hlv.le).mp hL
  have hGtotal : (∫ r in (0 : ℝ)..v, G r) = ∫ r in l..v, L r := by
    rw [intervalIntegral.integral_of_le hv.le]
    change (∫ r in Ioc (0 : ℝ) v, (Ioc l v).indicator L r) = _
    rw [MeasureTheory.integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, hset,
      intervalIntegral.integral_of_le hlv.le]
  have hmain := tendsto_integral_one_sub_sq_div_sq_mul_zero_left hv hG
  rw [hGtotal] at hmain
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hv).filter_mono nhdsWithin_le_nhds] with a ha hav
  have hprod : (fun r => (1 - a ^ 2 / r ^ 2) * G r) =
      (Ioc l v).indicator (fun r => (1 - a ^ 2 / r ^ 2) * L r) := by
    ext r
    simp only [G, Set.indicator_mul_right]
  rw [hprod, intervalIntegral.integral_of_le hav.le,
    MeasureTheory.integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  have hinter : Ioc l v ∩ Ioc a v = Ioc (max a l) v := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff]
    tauto
  rw [hinter, intervalIntegral.integral_of_le (max_le hav.le hlv.le)]

end intervalIntegral
