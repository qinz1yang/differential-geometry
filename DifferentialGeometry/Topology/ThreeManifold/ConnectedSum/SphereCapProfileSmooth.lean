import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapProfile
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology.SphereUnitFilling

def capPrimitive (ρ : ℝ) : ℝ := ∫ s in (1 : ℝ)..ρ, capDensity s

lemma capDensity_continuousAt {ρ : ℝ} (hρ : 0 < ρ) : ContinuousAt capDensity ρ :=
  contDiffOn_capDensity.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hρ)

lemma intervalIntegrable_capDensity {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    IntervalIntegrable capDensity volume a ρ := by
  refine ContinuousOn.intervalIntegrable ?_
  refine contDiffOn_capDensity.continuousOn.mono ?_
  intro y hy
  rcases le_total a ρ with h | h
  · rw [uIcc_of_le h] at hy
    exact lt_of_lt_of_le ha hy.1
  · rw [uIcc_of_ge h] at hy
    exact lt_of_lt_of_le hρ hy.1

lemma intervalIntegrable_capDensity_of_pos {ρ : ℝ} (hρ : 0 < ρ) :
    IntervalIntegrable capDensity volume (1 : ℝ) ρ :=
  intervalIntegrable_capDensity (by norm_num) hρ

lemma hasDerivAt_capPrimitive {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt capPrimitive (capDensity ρ) ρ :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_capDensity_of_pos hρ)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi contDiffOn_capDensity.continuousOn ρ hρ)
    (capDensity_continuousAt hρ)

lemma contDiffOn_capPrimitive : ContDiffOn ℝ ∞ capPrimitive (Ioi 0) := by
  refine (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr ⟨?_, ?_⟩
  · intro x hx
    exact (hasDerivAt_capPrimitive hx).differentiableAt.differentiableWithinAt
  · refine contDiffOn_capDensity.congr ?_
    intro x hx
    exact (hasDerivAt_capPrimitive hx).deriv

lemma hasDerivAt_capRadius {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt capRadius (-(capDensity ρ * capRadius ρ)) ρ := by
  have h := (hasDerivAt_capPrimitive hρ).neg.exp
  have heq : (fun y : ℝ => Real.exp (-(capPrimitive y))) =ᶠ[𝓝 ρ] capRadius :=
    Filter.Eventually.of_forall fun y => rfl
  have hval : Real.exp (-(capPrimitive ρ)) * (-(capDensity ρ)) =
      -(capDensity ρ * capRadius ρ) := by
    have hc : capRadius ρ = Real.exp (-(capPrimitive ρ)) := rfl
    rw [hc]; ring
  exact heq.hasDerivAt_iff.mp (h.congr_deriv hval)

lemma deriv_capRadius {ρ : ℝ} (hρ : 0 < ρ) :
    deriv capRadius ρ = -(capDensity ρ * capRadius ρ) :=
  (hasDerivAt_capRadius hρ).deriv

lemma deriv_capRadius_neg {ρ : ℝ} (hρ : 0 < ρ) : deriv capRadius ρ < 0 := by
  rw [deriv_capRadius hρ]
  nlinarith [capDensity_pos' ρ, capRadius_pos ρ]

lemma contDiffOn_capRadius : ContDiffOn ℝ ∞ capRadius (Ioi 0) :=
  ContDiffOn.exp contDiffOn_capPrimitive.neg

lemma contDiffAt_capRadius {ρ : ℝ} (hρ : 0 < ρ) : ContDiffAt ℝ ∞ capRadius ρ :=
  contDiffOn_capRadius.contDiffAt (isOpen_Ioi.mem_nhds hρ)

lemma capRadius_of_ge_seven_fourths {ρ : ℝ} (h : 7 / 4 ≤ ρ) :
    capRadius ρ = capRadius (7 / 4) * (7 / 4) / ρ := by
  have hcongr : (∫ s in (7 / 4 : ℝ)..ρ, capDensity s) = ∫ s in (7 / 4 : ℝ)..ρ, s⁻¹ := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    exact capDensity_of_le' (by
      have hs' : s ∈ Set.Icc (7 / 4 : ℝ) ρ := by simpa [uIcc_of_le h] using hs
      exact hs'.1)
  have hsplit : (∫ s in (1 : ℝ)..ρ, capDensity s) =
      (∫ s in (1 : ℝ)..(7 / 4), capDensity s) + ∫ s in (7 / 4)..ρ, capDensity s :=
    (intervalIntegral.integral_add_adjacent_intervals (a := (1 : ℝ)) (b := 7 / 4) (c := ρ)
      (intervalIntegrable_capDensity_of_pos (by norm_num))
      (intervalIntegrable_capDensity (a := 7 / 4) (by norm_num) (by linarith))).symm
  have hval : (∫ s in (7 / 4 : ℝ)..ρ, s⁻¹) = Real.log (ρ / (7 / 4)) :=
    integral_inv_of_pos (by norm_num) (by linarith)
  rw [capRadius, hsplit, hcongr, hval]
  have hexp : Real.exp (-((∫ s in (1 : ℝ)..(7 / 4), capDensity s) + Real.log (ρ / (7 / 4)))) =
      Real.exp (-(∫ s in (1 : ℝ)..(7 / 4), capDensity s)) * (7 / 4) / ρ := by
    have harg : -((∫ s in (1 : ℝ)..(7 / 4), capDensity s) + Real.log (ρ / (7 / 4))) =
        -(∫ s in (1 : ℝ)..(7 / 4), capDensity s) - Real.log (ρ / (7 / 4)) := by ring
    rw [harg, Real.exp_sub, Real.exp_log (by positivity)]
    field_simp
  rw [hexp]
  rfl

lemma tendsto_capRadius_atTop : Tendsto capRadius atTop (𝓝 0) := by
  have hbase : Tendsto (fun ρ : ℝ => capRadius (7 / 4) * (7 / 4) * ρ⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
  refine hbase.congr' (Filter.eventually_atTop.mpr ⟨7 / 4, fun ρ hρ => ?_⟩)
  rw [capRadius_of_ge_seven_fourths hρ]
  ring

lemma capRadius_mapsTo : MapsTo capRadius (Ici 1) (Ioc 0 1) := by
  intro ρ hρ
  exact ⟨capRadius_pos ρ, capRadius_le_one hρ⟩

lemma capRadius_two_div_of_mem {s : ℝ} (h1 : 4 / 3 ≤ s) (h2 : s ≤ 2) :
    capRadius (2 / s) = 2 - 2 / s := by
  have hpos : 0 < s := by linarith
  have hp : 1 ≤ 2 / s := by
    rw [le_div_iff₀ hpos]
    linarith
  have hq : 2 / s ≤ 3 / 2 := by
    rw [div_le_iff₀ hpos]
    linarith
  rw [capRadius_of_le hp hq]

lemma capRadius_two_div_of_le_eight_sevenths {s : ℝ} (hs : 0 < s) (h : s ≤ 8 / 7) :
    capRadius (2 / s) = capRadius 2 * s := by
  have hge : 7 / 4 ≤ 2 / s := by
    rw [le_div_iff₀ hs]
    linarith
  rw [capRadius_of_ge_seven_fourths hge]
  have h2 : capRadius 2 = capRadius (7 / 4) * (7 / 4) / 2 :=
    capRadius_of_ge_seven_fourths (by norm_num)
  rw [h2]
  field_simp

lemma capRadius_surjOn : SurjOn capRadius (Ici 1) (Ioc 0 1) := by
  intro y hy
  by_cases hy1 : y = 1
  · exact ⟨(1 : ℝ), le_refl (1 : ℝ), by rw [hy1, capRadius_one]⟩
  have hypos : 0 < y := hy.1
  let C : ℝ := capRadius (7 / 4) * (7 / 4)
  have hCpos : 0 < C := mul_pos (capRadius_pos (7 / 4)) (by norm_num)
  have hden : 0 < C / y + 1 := by positivity
  have hle : (1 : ℝ) ≤ max (7 / 4) (C / y + 1) :=
    le_trans (by norm_num : (1 : ℝ) ≤ 7 / 4) (le_max_left _ _)
  have hb : 7 / 4 ≤ max (7 / 4) (C / y + 1) := le_max_left _ _
  have hsmall : capRadius (max (7 / 4) (C / y + 1)) < y := by
    rw [capRadius_of_ge_seven_fourths hb]
    have h2 : C / max (7 / 4) (C / y + 1) ≤ C / (C / y + 1) :=
      div_le_div_of_nonneg_left (le_of_lt hCpos) hden (le_max_right _ _)
    have h3 : C / (C / y + 1) < y := by
      rw [div_lt_iff₀ hden]
      rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hypos), mul_one]
      linarith
    linarith
  have hcont : ContinuousOn capRadius (Icc (1 : ℝ) (max (7 / 4) (C / y + 1))) :=
    contDiffOn_capRadius.continuousOn.mono fun x hx => lt_of_lt_of_le (by norm_num) hx.1
  have hmem : y ∈ Icc (capRadius (max (7 / 4) (C / y + 1))) (capRadius 1) :=
    ⟨le_of_lt hsmall, by rw [capRadius_one]; exact hy.2⟩
  have hsub : y ∈ capRadius '' Icc (1 : ℝ) (max (7 / 4) (C / y + 1)) :=
    (intermediate_value_Icc' hle hcont) hmem
  obtain ⟨ρ, hρ, hρy⟩ := hsub
  exact ⟨ρ, hρ.1, hρy⟩

def capRadialScale (v : E3) : ℝ := capRadius (2 / ‖v‖) / ‖v‖

def capRadialMap (v : E3) : E3 := -(capRadialScale v) • v

lemma capRadialMap_eqOn_closedBall {v : E3} (hv : ‖v‖ ≤ 8 / 7) :
    capRadialMap v = -(capRadius 2) • v := by
  rcases eq_or_lt_of_le (norm_nonneg v) with h0 | h0
  · have hv0 : v = 0 := norm_eq_zero.mp h0.symm
    subst hv0
    simp [capRadialMap, capRadialScale]
  have hval : capRadialScale v = capRadius 2 := by
    rw [capRadialScale, capRadius_two_div_of_le_eight_sevenths h0 hv,
      mul_div_cancel_right₀ _ (ne_of_gt h0)]
  rw [capRadialMap, hval]

lemma contDiffAt_capRadialScale {v : E3} (hv : v ≠ 0) : ContDiffAt ℝ ∞ capRadialScale v := by
  have hne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnorm : ContDiffAt ℝ ∞ (fun w : E3 => ‖w‖) v := contDiffAt_norm (𝕜 := ℝ) hv
  have hpos : (0 : ℝ) < 2 / ‖v‖ := div_pos (by norm_num) (norm_pos_iff.mpr hv)
  have hdiv := (contDiff_const (c := (2 : ℝ))).contDiffAt.div hnorm hne
  exact ((contDiffAt_capRadius hpos).comp v hdiv).div hnorm hne

lemma contDiff_capRadialMap : ContDiff ℝ ∞ capRadialMap := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst hv
    have hev : capRadialMap =ᶠ[𝓝 (0 : E3)] (fun _ : E3 => -(capRadius 2)) • (id : E3 → E3) := by
      filter_upwards [Metric.ball_mem_nhds (0 : E3) (by norm_num : (0 : ℝ) < 8 / 7)]
        with w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact capRadialMap_eqOn_closedBall (le_of_lt hw)
    exact (contDiffAt_const.smul contDiffAt_id).congr_of_eventuallyEq hev
  · exact (contDiffAt_capRadialScale hv).neg.smul contDiffAt_id

lemma norm_capRadialMap {v : E3} (hv : 0 < ‖v‖) :
    ‖capRadialMap v‖ = capRadius (2 / ‖v‖) := by
  have hc : 0 ≤ capRadius (2 / ‖v‖) / ‖v‖ :=
    div_nonneg (le_of_lt (capRadius_pos _)) (le_of_lt hv)
  rw [capRadialMap, capRadialScale, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hc]
  field_simp

lemma norm_capRadialMap_le_one {v : E3} (hv : 0 < ‖v‖) (h2 : ‖v‖ ≤ 2) :
    ‖capRadialMap v‖ ≤ 1 := by
  rw [norm_capRadialMap hv]
  refine capRadius_le_one ?_
  rw [le_div_iff₀ hv]
  linarith

lemma capRadialMap_two_smul {z : E3} (hz : ‖z‖ = 1) : capRadialMap ((2 : ℝ) • z) = -z := by
  have hnorm : ‖(2 : ℝ) • z‖ = 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hz, mul_one]
  have htwo : (2 : ℝ) / 2 = 1 := by norm_num
  rw [capRadialMap, capRadialScale, hnorm, htwo, capRadius_one]
  module

lemma capRadialMap_two_div_smul {z : E3} (hz : ‖z‖ = 1) {ρ : ℝ} (h1 : 1 ≤ ρ) :
    capRadialMap ((2 / ρ) • z) = -(capRadius ρ) • z := by
  have hpos : 0 < ρ := by linarith
  have hnorm : ‖(2 / ρ) • z‖ = 2 / ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hz, mul_one]
  have htwo : 2 / (2 / ρ) = ρ := by
    field_simp
  rw [capRadialMap, capRadialScale, hnorm, htwo]
  rw [smul_smul]
  congr 1
  field_simp

lemma capRadialMap_two_div_smul_of_le {z : E3} (hz : ‖z‖ = 1) {ρ : ℝ} (h1 : 1 ≤ ρ)
    (h2 : ρ ≤ 3 / 2) : capRadialMap ((2 / ρ) • z) = (ρ - 2) • z := by
  rw [capRadialMap_two_div_smul hz h1, capRadius_of_le h1 h2]
  congr 1
  ring

lemma capRadialMap_surjOn :
    SurjOn capRadialMap (Metric.closedBall (0 : E3) 2) (Metric.closedBall (0 : E3) 1) := by
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | h0
  · have hw0 : w = 0 := norm_eq_zero.mp h0.symm
    refine ⟨0, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      norm_num
    · rw [hw0]
      simp [capRadialMap]
  · obtain ⟨ρ, hρ, hρw⟩ := capRadius_surjOn ⟨h0, hw⟩
    have hρ1 : (1 : ℝ) ≤ ρ := hρ
    have hρpos : (0 : ℝ) < ρ := by linarith
    have hz : ‖-(‖w‖⁻¹ • w)‖ = 1 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (le_of_lt h0)), inv_mul_cancel₀ (ne_of_gt h0)]
    refine ⟨(2 / ρ) • (-(‖w‖⁻¹ • w)), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / ρ), hz, mul_one]
      rw [div_le_iff₀ hρpos]
      linarith
    · rw [capRadialMap_two_div_smul hz hρ, hρw]
      rw [← neg_smul, smul_smul, neg_mul_neg, mul_inv_cancel₀ (ne_of_gt h0), one_smul]

lemma capRadialMap_injOn : InjOn capRadialMap (Metric.closedBall (0 : E3) 2) := by
  intro v hv v' hv' heq
  rw [Metric.mem_closedBall, dist_zero_right] at hv hv'
  rcases eq_or_lt_of_le (norm_nonneg v) with h0 | h0
  · have hv0 : v = 0 := norm_eq_zero.mp h0.symm
    subst hv0
    rcases eq_or_lt_of_le (norm_nonneg v') with h0' | h0'
    · exact (norm_eq_zero.mp h0'.symm).symm
    · have hzero : ‖capRadialMap v'‖ = 0 := by rw [← heq]; simp [capRadialMap]
      rw [norm_capRadialMap h0'] at hzero
      exact absurd hzero (ne_of_gt (capRadius_pos _))
  · rcases eq_or_lt_of_le (norm_nonneg v') with h0' | h0'
    · have hv'0 : v' = 0 := norm_eq_zero.mp h0'.symm
      subst hv'0
      have hzero : ‖capRadialMap v‖ = 0 := by rw [heq]; simp [capRadialMap]
      rw [norm_capRadialMap h0] at hzero
      exact absurd hzero (ne_of_gt (capRadius_pos _))
    · have hdec : ∀ u : E3, capRadialMap u = -(capRadius (2 / ‖u‖)) • (‖u‖⁻¹ • u) := by
        intro u
        rw [capRadialMap, capRadialScale, smul_smul]
        congr 1
        ring
      have h1 : (1 : ℝ) ≤ 2 / ‖v‖ := by rw [le_div_iff₀ h0]; linarith
      have h2 : (1 : ℝ) ≤ 2 / ‖v'‖ := by rw [le_div_iff₀ h0']; linarith
      have hnorm : capRadius (2 / ‖v‖) = capRadius (2 / ‖v'‖) := by
        rw [← norm_capRadialMap h0, ← norm_capRadialMap h0', heq]
      have hscalar : 2 / ‖v‖ = 2 / ‖v'‖ := capRadius_injOn h1 h2 hnorm
      have hs : ‖v‖ = ‖v'‖ := by
        have h := hscalar
        rw [div_eq_div_iff (ne_of_gt h0) (ne_of_gt h0')] at h
        linarith
      have hcancel : ‖v‖⁻¹ • v = ‖v'‖⁻¹ • v' := by
        have hkey : -(capRadius (2 / ‖v'‖)) • (‖v‖⁻¹ • v) =
            -(capRadius (2 / ‖v'‖)) • (‖v'‖⁻¹ • v') := by
          have h := heq
          rw [hdec v, hdec v', hnorm] at h
          exact h
        exact smul_right_injective (M := E3)
          (neg_ne_zero.mpr (ne_of_gt (capRadius_pos _))) hkey
      calc v = ‖v‖ • (‖v‖⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ (ne_of_gt h0), one_smul]
        _ = ‖v‖ • (‖v'‖⁻¹ • v') := by rw [hcancel]
        _ = (‖v‖ * ‖v'‖⁻¹) • v' := by rw [smul_smul]
        _ = v' := by rw [hs, mul_inv_cancel₀ (ne_of_gt h0'), one_smul]

lemma capRadialMap_image_closedBall :
    capRadialMap '' Metric.closedBall (0 : E3) 2 = Metric.closedBall (0 : E3) 1 := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro w ⟨v, hv, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hv ⊢
    rcases eq_or_lt_of_le (norm_nonneg v) with h0 | h0
    · have hv0 : v = 0 := norm_eq_zero.mp h0.symm
      rw [hv0]
      simp [capRadialMap]
    · exact norm_capRadialMap_le_one h0 hv
  · intro w hw
    exact capRadialMap_surjOn hw

end DifferentialGeometry.Topology.SphereUnitFilling
