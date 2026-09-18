import DifferentialGeometry.Analysis.Integration.Fatou
import DifferentialGeometry.Analysis.Integration.Convolution.SecondDifference
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Module

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Convolution Pointwise Topology

namespace ConcaveOn

private theorem convolution_nonneg_left
    {f phi : Real → Real} (hf : ConcaveOn Real univ f)
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi)
    (hphi_nonneg : ∀ x, 0 ≤ phi x) :
    ConcaveOn Real univ (phi ⋆[ContinuousLinearMap.mul Real Real] f) := by
  have hfcont : Continuous f :=
    continuousOn_univ.mp (ConcaveOn.continuousOn isOpen_univ hf)
  have hint : ∀ x : Real, Integrable (fun t ↦ phi t * f (x - t)) := by
    intro x
    simpa only [MeasureTheory.ConvolutionExistsAt, ContinuousLinearMap.mul_apply'] using
      hsupp.convolutionExists_left (ContinuousLinearMap.mul Real Real)
        hphi hfcont.locallyIntegrable x
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul, MeasureTheory.convolution_def,
    ContinuousLinearMap.mul_apply']
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint x).const_mul a) ((hint y).const_mul b)]
  apply integral_mono
    (((hint x).const_mul a).add ((hint y).const_mul b)) (hint (a * x + b * y))
  intro t
  have hconc := hf.2 (mem_univ (x - t)) (mem_univ (y - t)) ha hb hab
  simp only [smul_eq_mul] at hconc
  have harg : a * (x - t) + b * (y - t) = a * x + b * y - t := by
    calc
      _ = a * x + b * y - (a + b) * t := by ring
      _ = _ := by rw [hab, one_mul]
  rw [harg] at hconc
  calc
    _ = phi t * (a * f (x - t) + b * f (y - t)) := by
      simp only [Pi.add_apply]
      ring
    _ ≤ phi t * f (a * x + b * y - t) :=
      mul_le_mul_of_nonneg_left hconc (hphi_nonneg t)

theorem integral_mul_deriv_deriv_nonpos
    {f phi : Real → Real} (hf : ConcaveOn Real univ f)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hphi_nonneg : ∀ x, 0 ≤ phi x) :
    (∫ x, f x * deriv (deriv phi) x) ≤ 0 := by
  let g : Real → Real := fun x ↦ f (-x)
  have hg : ConcaveOn Real univ g := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := hf.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
    simpa only [g, smul_eq_mul, mul_neg, ← neg_add] using h
  have hgcont : Continuous g :=
    continuousOn_univ.mp (ConcaveOn.continuousOn isOpen_univ hg)
  let F : Real → Real := phi ⋆[ContinuousLinearMap.mul Real Real] g
  have hF : ContDiff Real 2 F :=
    hsupp.contDiff_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi hgcont.locallyIntegrable
  have hFconc : ConcaveOn Real univ F :=
    convolution_nonneg_left hg hphi.continuous hsupp hphi_nonneg
  have hFanti : Antitone (deriv F) :=
    antitoneOn_univ.mp (hFconc.antitoneOn_deriv
      (fun x _ ↦ (hF.differentiable (by norm_num)).differentiableAt))
  have hnonpos : deriv (deriv F) 0 ≤ 0 := hFanti.deriv_nonpos
  have hphi_one : ContDiff Real 1 phi := hphi.of_le (by norm_num)
  have hphi_deriv_one : ContDiff Real 1 (deriv phi) := by
    exact hphi.deriv'
  have hFderiv : deriv F =
      deriv phi ⋆[ContinuousLinearMap.mul Real Real] g := by
    funext x
    exact (hsupp.hasDerivAt_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi_one hgcont.locallyIntegrable x).deriv
  have hFsecond : deriv (deriv F) 0 =
      (deriv (deriv phi) ⋆[ContinuousLinearMap.mul Real Real] g) 0 := by
    rw [hFderiv]
    exact (hsupp.deriv.hasDerivAt_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi_deriv_one hgcont.locallyIntegrable 0).deriv
  rw [hFsecond] at hnonpos
  simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply',
    zero_sub, g, neg_neg, mul_comm] using hnonpos

theorem integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae
    {f phi q : Real → Real} (hf : ConcaveOn Real univ f)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hphi_nonneg : ∀ x, 0 ≤ phi x)
    (h : Nat → Real) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0)
    (hq : Integrable (fun x ↦ q x * phi x))
    (hlim : ∀ᵐ x ∂volume, Tendsto
      (fun n ↦ (f (x + h n) - 2 * f x + f (x - h n)) / (h n) ^ 2)
      atTop (𝓝 (q x))) :
    (∫ x, f x * deriv (deriv phi) x) ≤ ∫ x, q x * phi x := by
  have hfcont : Continuous f :=
    continuousOn_univ.mp (ConcaveOn.continuousOn isOpen_univ hf)
  let g : Real → Real := fun x ↦ f (-x)
  have hgcont : Continuous g := hfcont.comp continuous_neg
  let F : Real → Real := phi ⋆[ContinuousLinearMap.mul Real Real] g
  have hF : ContDiff Real 2 F :=
    hsupp.contDiff_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi hgcont.locallyIntegrable
  have hphi_one : ContDiff Real 1 phi := hphi.of_le (by norm_num)
  have hphi_deriv_one : ContDiff Real 1 (deriv phi) := hphi.deriv'
  have hFderiv : deriv F =
      deriv phi ⋆[ContinuousLinearMap.mul Real Real] g := by
    funext x
    exact (hsupp.hasDerivAt_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi_one hgcont.locallyIntegrable x).deriv
  have hFsecond : deriv (deriv F) 0 = ∫ x, f x * deriv (deriv phi) x := by
    rw [hFderiv]
    have hraw := (hsupp.deriv.hasDerivAt_convolution_left
      (μ := volume) (ContinuousLinearMap.mul Real Real) hphi_deriv_one
      hgcont.locallyIntegrable 0).deriv
    simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply',
      g, zero_sub, neg_neg, mul_comm] using hraw
  have hFvalue : ∀ a, F a = ∫ x, f (x - a) * phi x := by
    intro a
    simp only [F, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', g]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by simp only [neg_sub, mul_comm]
  let D : Nat → Real → Real := fun n x ↦
    (f (x + h n) - 2 * f x + f (x - h n)) / (h n) ^ 2 * phi x
  have hDint : ∀ n, Integrable (D n) := by
    intro n
    have hcont : Continuous (D n) := by
      dsimp only [D]
      fun_prop
    exact hcont.integrable_of_hasCompactSupport hsupp.mul_left
  have hDnonpos : ∀ n, ∀ x, D n x ≤ 0 := by
    intro n x
    have hconc := hf.2 (mem_univ (x + h n)) (mem_univ (x - h n))
      (show (0 : Real) ≤ 1 / 2 by norm_num)
      (show (0 : Real) ≤ 1 / 2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hconc
    have hmid : (1 / 2 : Real) * (x + h n) + 1 / 2 * (x - h n) = x := by ring
    rw [hmid] at hconc
    have hnum : f (x + h n) - 2 * f x + f (x - h n) ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg (h n))) (hphi_nonneg x)
  have hpair : ∀ n, (∫ x, D n x) =
      (F (h n) - 2 * F 0 + F (-h n)) / (h n) ^ 2 := by
    intro n
    have hp : Integrable (fun x ↦ f (x + h n) * phi x) := by
      apply Continuous.integrable_of_hasCompactSupport _ hsupp.mul_left
      exact (hfcont.comp (continuous_id.add continuous_const)).mul hphi.continuous
    have hm : Integrable (fun x ↦ f (x - h n) * phi x) := by
      apply Continuous.integrable_of_hasCompactSupport _ hsupp.mul_left
      exact (hfcont.comp (continuous_id.sub continuous_const)).mul hphi.continuous
    have hz : Integrable (fun x ↦ f x * phi x) :=
      (hfcont.mul hphi.continuous).integrable_of_hasCompactSupport hsupp.mul_left
    calc
      (∫ x, D n x) =
          ∫ x, ((f (x + h n) * phi x - 2 * (f x * phi x)) +
            f (x - h n) * phi x) / (h n) ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by dsimp only [D]; ring
      _ = ((∫ x, f (x + h n) * phi x) - 2 * (∫ x, f x * phi x) +
          (∫ x, f (x - h n) * phi x)) / (h n) ^ 2 := by
        have hadd := integral_add (hp.sub (hz.const_mul 2)) hm
        have hsub := integral_sub hp (hz.const_mul 2)
        simp only [Pi.sub_apply] at hadd hsub
        rw [integral_div, hadd, hsub, integral_const_mul]
      _ = _ := by
        rw [hFvalue, hFvalue, hFvalue]
        simp only [sub_zero, sub_neg_eq_add]
        ring
  have hhne : Tendsto h atTop (𝓝[≠] (0 : Real)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Eventually.of_forall hne⟩
  have hpairlim : Tendsto (fun n ↦ ∫ x, D n x) atTop
      (𝓝 (∫ x, f x * deriv (deriv phi) x)) := by
    have hraw := (hF.tendsto_centered_second_difference 0).comp hhne
    simp only [Function.comp_def, zero_add, zero_sub, hFsecond] at hraw
    exact hraw.congr (fun n ↦ (hpair n).symm)
  apply MeasureTheory.tendsto_integral_le_integral_of_nonpos hDint hq
    (fun n ↦ Eventually.of_forall (hDnonpos n)) ?_ hpairlim
  filter_upwards [hlim] with x hx
  exact hx.mul_const (phi x)

end ConcaveOn

namespace DifferentialGeometry.Analysis

theorem integral_mul_deriv_deriv_le_of_concaveOn_sub_quadratic
    {f phi q : Real → Real} {U : Set Real} (C : Real)
    (hf : ConcaveOn Real U (fun x ↦ f x - C * x ^ 2 / 2)) (hU : IsOpen U)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hsuppU : tsupport phi ⊆ U) (hphi_nonneg : ∀ x, 0 ≤ phi x)
    (h : Nat → Real) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0)
    (hq : Integrable (fun x ↦ q x * phi x))
    (hlim : ∀ᵐ x ∂volume, x ∈ U → Tendsto
      (fun n ↦ (f (x + h n) - 2 * f x + f (x - h n)) / (h n) ^ 2)
      atTop (𝓝 (q x))) :
    (∫ x, f x * deriv (deriv phi) x) ≤ ∫ x, q x * phi x := by
  classical
  obtain ⟨V, hV, hVU⟩ := compact_open_separated_add_right hsupp.isCompact hU hsuppU
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hV
  let delta : Real := epsilon / 2
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  let K : Set Real := tsupport phi + Metric.closedBall 0 delta
  have hK : IsCompact K := hsupp.isCompact.add (isCompact_closedBall 0 delta)
  have hKU : K ⊆ U := by
    intro z hz
    rcases hz with ⟨x, hx, v, hv, rfl⟩
    apply hVU
    refine ⟨x, hx, v, hball ?_, rfl⟩
    apply Metric.mem_ball.mpr
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hv) (by dsimp only [delta]; linarith)
  have hsuppK : tsupport phi ⊆ K := by
    intro x hx
    exact ⟨x, hx, 0, Metric.mem_closedBall_self hdelta.le, add_zero x⟩
  have hshift : ∀ x ∈ tsupport phi, ∀ a : Real, |a| ≤ delta →
      x + a ∈ K ∧ x - a ∈ K := by
    intro x hx a ha
    constructor
    · exact ⟨x, hx, a, by simpa only [Metric.mem_closedBall, dist_zero_right,
        Real.norm_eq_abs] using ha, rfl⟩
    · exact ⟨x, hx, -a, by simpa only [Metric.mem_closedBall, dist_zero_right,
        Real.norm_eq_abs, abs_neg] using ha, (sub_eq_add_neg x a).symm⟩
  have hpoly : Continuous (fun x : Real ↦ C * x ^ 2 / 2) := by fun_prop
  have hfcont : ContinuousOn f U := by
    have hsum : ContinuousOn (fun x ↦ (f x - C * x ^ 2 / 2) + C * x ^ 2 / 2) U :=
      (ConcaveOn.continuousOn hU hf).add hpoly.continuousOn
    simpa only [sub_add_cancel] using hsum
  let F : Real → Real := K.indicator f
  have hFint : Integrable F :=
    (ContinuousOn.integrableOn_compact hK (hfcont.mono hKU)).integrable_indicator
      hK.measurableSet
  have hsmall : ∀ᶠ n in atTop, |h n| ≤ delta := by
    have hevent := hh (Metric.ball_mem_nhds (0 : Real) hdelta)
    filter_upwards [hevent] with n hn
    have hnabs : |h n| < delta := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hn
    exact hnabs.le
  let D : Nat → Real → Real := fun n x ↦
    (F (x + h n) - 2 * F x + F (x - h n)) / (h n) ^ 2 * phi x
  have hDint : ∀ n, Integrable (D n) := by
    intro n
    have hraw : Integrable (fun x ↦
        (F (x + h n) - 2 * F x + F (x - h n)) / (h n) ^ 2) :=
      (((hFint.comp_add_right (h n)).sub (hFint.const_mul 2)).add
        (hFint.comp_sub_right (h n))).div_const _
    simpa only [D, smul_eq_mul] using
      hraw.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hphi.continuous hsupp
  have hDevent : ∀ᶠ n in atTop, ∀ᵐ x ∂volume, D n x ≤ C * phi x := by
    filter_upwards [hsmall] with n hn
    apply Eventually.of_forall
    intro x
    by_cases hx : phi x = 0
    · simp only [D, hx, mul_zero, le_refl]
    have hxK : x ∈ tsupport phi := subset_tsupport phi hx
    have hplus := (hshift x hxK (h n) hn).1
    have hminus := (hshift x hxK (h n) hn).2
    have hconc := hf.2 (hKU hplus) (hKU hminus)
      (show (0 : Real) ≤ 1 / 2 by norm_num)
      (show (0 : Real) ≤ 1 / 2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hconc
    have hmid : (1 / 2 : Real) * (x + h n) + 1 / 2 * (x - h n) = x := by ring
    rw [hmid] at hconc
    have hnum : f (x + h n) - 2 * f x + f (x - h n) ≤ C * (h n) ^ 2 := by
      nlinarith [hconc]
    dsimp only [D, F]
    rw [indicator_of_mem hplus, indicator_of_mem (hsuppK hxK), indicator_of_mem hminus]
    exact mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (sq_pos_of_ne_zero (hne n))).mpr hnum) (hphi_nonneg x)
  have hDlim : ∀ᵐ x ∂volume,
      Tendsto (fun n ↦ D n x) atTop (𝓝 (q x * phi x)) := by
    filter_upwards [hlim] with x hx
    by_cases hxzero : phi x = 0
    · simpa only [D, hxzero, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : Nat ↦ (0 : Real)) atTop (𝓝 0))
    have hxK : x ∈ tsupport phi := subset_tsupport phi hxzero
    apply ((hx (hsuppU hxK)).mul_const (phi x)).congr'
    filter_upwards [hsmall] with n hn
    have hplus := (hshift x hxK (h n) hn).1
    have hminus := (hshift x hxK (h n) hn).2
    simp only [D, F, indicator_of_mem hplus,
      indicator_of_mem (hsuppK hxK), indicator_of_mem hminus]
  have hpair := hFint.tendsto_integral_mul_centered_second_difference hphi hsupp h hh hne
  have hCint : Integrable (fun x ↦ C * phi x) :=
    (hphi.continuous.integrable_of_hasCompactSupport hsupp).const_mul C
  have hbound := MeasureTheory.tendsto_integral_le_integral_of_eventually_le
    hDint hq hCint hDevent hDlim hpair
  have heq : (∫ x, F x * deriv (deriv phi) x) =
      ∫ x, f x * deriv (deriv phi) x := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport phi
    · simp only [F, indicator_of_mem (hsuppK hx)]
    · have hx' : x ∉ tsupport (deriv phi) :=
        fun hmem ↦ hx (tsupport_deriv_subset hmem)
      simp only [deriv_of_notMem_tsupport hx', mul_zero]
  rwa [heq] at hbound

end DifferentialGeometry.Analysis

namespace ConcaveOn

theorem integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae_on
    {f phi q : Real → Real} {U : Set Real}
    (hf : ConcaveOn Real U f) (hU : IsOpen U)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hsuppU : tsupport phi ⊆ U) (hphi_nonneg : ∀ x, 0 ≤ phi x)
    (h : Nat → Real) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0)
    (hq : Integrable (fun x ↦ q x * phi x))
    (hlim : ∀ᵐ x ∂volume, x ∈ U → Tendsto
      (fun n ↦ (f (x + h n) - 2 * f x + f (x - h n)) / (h n) ^ 2)
      atTop (𝓝 (q x))) :
    (∫ x, f x * deriv (deriv phi) x) ≤ ∫ x, q x * phi x := by
  have hfzero : ConcaveOn Real U (fun x ↦ f x - (0 : Real) * x ^ 2 / 2) := by
    simpa only [zero_mul, zero_div, sub_zero] using hf
  exact DifferentialGeometry.Analysis.integral_mul_deriv_deriv_le_of_concaveOn_sub_quadratic
    0 hfzero hU hphi hsupp hsuppU hphi_nonneg h hh hne hq hlim

end ConcaveOn

namespace DifferentialGeometry.Analysis

theorem integral_mul_fderiv_fderiv_le_of_concaveOn_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] {mu : Measure E}
    [SFinite mu] [mu.IsAddLeftInvariant] [mu.IsNegInvariant] [IsFiniteMeasureOnCompacts mu]
    {f phi q : E → Real} {U : Set E} (B : E →L[Real] E →L[Real] Real)
    (hf : ConcaveOn Real U (fun x ↦ f x - B x x / 2)) (hU : IsOpen U)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hsuppU : tsupport phi ⊆ U) (hphi_nonneg : ∀ x, 0 ≤ phi x) (v : E)
    (h : Nat → Real) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0)
    (hq : Integrable (fun x ↦ q x * phi x) mu)
    (hlim : ∀ᵐ x ∂mu, x ∈ U → Tendsto
      (fun n ↦ (f (x + h n • v) - 2 * f x + f (x - h n • v)) / (h n) ^ 2)
      atTop (𝓝 (q x))) :
    (∫ x, f x * fderiv Real (fun y ↦ fderiv Real phi y v) x v ∂mu) ≤
      ∫ x, q x * phi x ∂mu := by
  classical
  obtain ⟨V, hV, hVU⟩ := compact_open_separated_add_right hsupp.isCompact hU hsuppU
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hV
  let delta : Real := epsilon / 2
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  let K : Set E := tsupport phi + Metric.closedBall 0 delta
  have hK : IsCompact K := hsupp.isCompact.add (isCompact_closedBall 0 delta)
  have hKU : K ⊆ U := by
    intro z hz
    rcases hz with ⟨x, hx, w, hw, rfl⟩
    apply hVU
    refine ⟨x, hx, w, hball ?_, rfl⟩
    apply Metric.mem_ball.mpr
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by dsimp only [delta]; linarith)
  have hsuppK : tsupport phi ⊆ K := by
    intro x hx
    exact ⟨x, hx, 0, Metric.mem_closedBall_self hdelta.le, add_zero x⟩
  have hshift : ∀ x ∈ tsupport phi, ∀ w : E, ‖w‖ ≤ delta →
      x + w ∈ K ∧ x - w ∈ K := by
    intro x hx w hw
    constructor
    · exact ⟨x, hx, w, by simpa only [Metric.mem_closedBall, dist_zero_right] using hw, rfl⟩
    · exact ⟨x, hx, -w, by simpa only [Metric.mem_closedBall, dist_zero_right,
        norm_neg] using hw, (sub_eq_add_neg x w).symm⟩
  have hpoly : Continuous (fun x : E ↦ B x x / 2) := by fun_prop
  have hfcont : ContinuousOn f U := by
    have hsum : ContinuousOn (fun x ↦ (f x - B x x / 2) + B x x / 2) U :=
      (ConcaveOn.continuousOn hU hf).add hpoly.continuousOn
    simpa only [sub_add_cancel] using hsum
  let F : E → Real := K.indicator f
  have hFint : Integrable F mu :=
    (ContinuousOn.integrableOn_compact hK (hfcont.mono hKU)).integrable_indicator
      hK.measurableSet
  have hsmall : ∀ᶠ n in atTop, ‖h n • v‖ ≤ delta := by
    have hvec : Tendsto (fun n ↦ h n • v) atTop (𝓝 (0 : E)) := by
      simpa only [zero_smul] using hh.smul_const v
    have hevent := hvec (Metric.ball_mem_nhds (0 : E) hdelta)
    filter_upwards [hevent] with n hn
    have hnorm : ‖h n • v‖ < delta := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hn
    exact hnorm.le
  let D : Nat → E → Real := fun n x ↦
    (F (x + h n • v) - 2 * F x + F (x - h n • v)) / (h n) ^ 2 * phi x
  have hDint : ∀ n, Integrable (D n) mu := by
    intro n
    have hraw : Integrable (fun x ↦
        (F (x + h n • v) - 2 * F x + F (x - h n • v)) / (h n) ^ 2) mu :=
      (((hFint.comp_add_right (h n • v)).sub (hFint.const_mul 2)).add
        (hFint.comp_sub_right (h n • v))).div_const _
    simpa only [D, smul_eq_mul] using
      hraw.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hphi.continuous hsupp
  have hDevent : ∀ᶠ n in atTop, ∀ᵐ x ∂mu, D n x ≤ B v v * phi x := by
    filter_upwards [hsmall] with n hn
    apply Eventually.of_forall
    intro x
    by_cases hx : phi x = 0
    · simp only [D, hx, mul_zero, le_refl]
    have hxK : x ∈ tsupport phi := subset_tsupport phi hx
    have hplus := (hshift x hxK (h n • v) hn).1
    have hminus := (hshift x hxK (h n • v) hn).2
    have hconc := hf.2 (hKU hplus) (hKU hminus)
      (show (0 : Real) ≤ 1 / 2 by norm_num)
      (show (0 : Real) ≤ 1 / 2 by norm_num) (by norm_num)
    have hmid : (1 / 2 : Real) • (x + h n • v) + (1 / 2 : Real) • (x - h n • v) = x := by
      module
    rw [hmid] at hconc
    simp only [smul_eq_mul, map_add, map_sub, map_smul,
      add_apply, sub_apply, smul_apply] at hconc
    have hnum : f (x + h n • v) - 2 * f x + f (x - h n • v) ≤
        B v v * (h n) ^ 2 := by nlinarith [hconc]
    dsimp only [D, F]
    rw [indicator_of_mem hplus, indicator_of_mem (hsuppK hxK), indicator_of_mem hminus]
    exact mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (sq_pos_of_ne_zero (hne n))).mpr hnum) (hphi_nonneg x)
  have hDlim : ∀ᵐ x ∂mu,
      Tendsto (fun n ↦ D n x) atTop (𝓝 (q x * phi x)) := by
    filter_upwards [hlim] with x hx
    by_cases hxzero : phi x = 0
    · simpa only [D, hxzero, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : Nat ↦ (0 : Real)) atTop (𝓝 0))
    have hxK : x ∈ tsupport phi := subset_tsupport phi hxzero
    apply ((hx (hsuppU hxK)).mul_const (phi x)).congr'
    filter_upwards [hsmall] with n hn
    have hplus := (hshift x hxK (h n • v) hn).1
    have hminus := (hshift x hxK (h n • v) hn).2
    simp only [D, F, indicator_of_mem hplus,
      indicator_of_mem (hsuppK hxK), indicator_of_mem hminus]
  have hpair := hFint.tendsto_integral_mul_directional_second_difference
    hphi hsupp v h hh hne
  have hBint : Integrable (fun x ↦ B v v * phi x) mu :=
    (hphi.continuous.integrable_of_hasCompactSupport hsupp).const_mul (B v v)
  have hbound := MeasureTheory.tendsto_integral_le_integral_of_eventually_le
    hDint hq hBint hDevent hDlim hpair
  have heq : (∫ x, F x * fderiv Real (fun y ↦ fderiv Real phi y v) x v ∂mu) =
      ∫ x, f x * fderiv Real (fun y ↦ fderiv Real phi y v) x v ∂mu := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport phi
    · simp only [F, indicator_of_mem (hsuppK hx)]
    · have hx' : x ∉ tsupport (fun y ↦ fderiv Real phi y v) :=
        fun hmem ↦ hx (tsupport_fderiv_apply_subset Real v hmem)
      simp only [fderiv_of_notMem_tsupport Real hx', zero_apply, mul_zero]
  rwa [heq] at hbound

end DifferentialGeometry.Analysis

end
