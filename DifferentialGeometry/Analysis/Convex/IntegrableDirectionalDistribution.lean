import DifferentialGeometry.Analysis.Convex.Distribution
import DifferentialGeometry.Analysis.Integration.Integral.OneSidedFatou


noncomputable section

open Filter MeasureTheory Set
open scoped Convolution Pointwise Topology

namespace DifferentialGeometry.Analysis

theorem integrable_mul_and_integral_mul_fderiv_fderiv_le_of_concaveOn_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] {mu : Measure E}
    [SFinite mu] [mu.IsAddLeftInvariant] [mu.IsNegInvariant] [IsFiniteMeasureOnCompacts mu]
    {f phi q : E → Real} {U : Set E} (B : E →L[Real] E →L[Real] Real)
    (hf : ConcaveOn Real U (fun x ↦ f x - B x x / 2)) (hU : IsOpen U)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hsuppU : tsupport phi ⊆ U) (hphi_nonneg : ∀ x, 0 ≤ phi x) (v : E)
    (h : Nat → Real) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0)
    (hlim : ∀ᵐ x ∂mu, x ∈ U → Tendsto
      (fun n ↦ (f (x + h n • v) - 2 * f x + f (x - h n • v)) / (h n) ^ 2)
      atTop (𝓝 (q x))) :
    Integrable (fun x ↦ q x * phi x) mu ∧
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
  have hq := MeasureTheory.integrable_of_tendsto_integral_of_eventually_le
    hDint hBint hDevent hDlim hpair
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
  exact ⟨hq, by rwa [heq] at hbound⟩

end DifferentialGeometry.Analysis
