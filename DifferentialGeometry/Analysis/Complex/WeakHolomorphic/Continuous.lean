import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Module

set_option autoImplicit false
noncomputable section

open Set Filter Metric MeasureTheory Function
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

private theorem normed_bump_convolution_tendstoLocallyUniformly
    (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {F : ℂ → V} (hF : Continuous F) :
    TendstoLocallyUniformly
      (fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F)
      F atTop := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro z
  have hconv : Tendsto (fun q : ℕ × ℂ =>
      (((φ q.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) q.2))
      (atTop ×ˢ 𝓝 z) (𝓝 (F z)) :=
    ContDiffBump.convolution_tendsto_right
      (hφ.comp tendsto_fst)
      (Eventually.of_forall fun _ => hF.aestronglyMeasurable)
      ((hF.tendsto z).comp tendsto_snd) tendsto_snd
  exact (Uniform.tendsto_nhds_left.mp ((hF.tendsto z).comp tendsto_snd)).uniformity_trans
    (Uniform.tendsto_nhds_right.mp hconv)

omit [CompleteSpace V] in
private theorem convolution_fderiv_apply
    {F : ℂ → V} (hF : Continuous F) {ρ : ℂ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (z v : ℂ) :
    fderiv ℝ (F ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] ρ) z v =
      ∫ y : ℂ, (fderiv ℝ ρ (z - y) v) • F y := by
  have hd := hc.hasFDerivAt_convolution_right
    (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (μ := (volume : Measure ℂ))
    hF.locallyIntegrable
    (hρ.of_le (by simp)) z
  rw [hd.fderiv, convolution_precompR_apply
    (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip) hF.locallyIntegrable
    (hc.fderiv ℝ) (hρ.continuous_fderiv (by simp)) z v]
  rfl

private theorem reflected_test_fderiv
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (z y v : ℂ) :
    fderiv ℝ (fun t => ρ (z - t)) y v = -(fderiv ℝ ρ (z - y) v) := by
  have hd := ((hρ.differentiable (by simp)) (z - y)).hasFDerivAt.comp y
    ((hasFDerivAt_const z y).sub (hasFDerivAt_id y))
  change (fderiv ℝ (ρ ∘ fun t => z - t) y) v = _
  rw [hd.fderiv]
  simp

omit [CompleteSpace V] in
private theorem differentiableAt_convolution_of_weak_dbar_zero
    {Ω : Set ℂ} {F : ℂ → V} (hF : Continuous F)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ y : ℂ, (((fderiv ℝ φ y (1 : ℂ) : ℂ) +
        Complex.I * (fderiv ℝ φ y Complex.I : ℂ)) / 2) • F y) = 0)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (z : ℂ)
    (hsupport : ∀ y, z - y ∈ tsupport ρ → y ∈ Ω) :
    DifferentiableAt ℂ (F ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] ρ) z := by
  let T : ℂ ≃ₜ ℂ := (Homeomorph.neg ℂ).trans (Homeomorph.addLeft z)
  let ψ : ℂ → ℝ := fun y => ρ (z - y)
  have hψ : ContDiff ℝ ∞ ψ := hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := by
    change HasCompactSupport (ρ ∘ T)
    exact hc.comp_homeomorph T
  have hψs : tsupport ψ ⊆ Ω := by
    intro y hy
    apply hsupport y
    change y ∈ tsupport (ρ ∘ T) at hy
    exact tsupport_comp_subset_preimage ρ T.continuous hy
  have hw := hweak ψ hψ hψc hψs
  let D (v y : ℂ) : V := (fderiv ℝ ρ (z - y) v) • F y
  have hDi (v : ℂ) : Integrable (D v) := by
    apply hF.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    · exact ((hρ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_const.sub continuous_id)
    · change HasCompactSupport ((fun y => fderiv ℝ ρ y v) ∘ T)
      exact (hc.fderiv_apply (𝕜 := ℝ) v).comp_homeomorph T
  have htest : (fun y => (((fderiv ℝ ψ y (1 : ℂ) : ℂ) +
      Complex.I * (fderiv ℝ ψ y Complex.I : ℂ)) / 2) • F y) =
      (fun y => (- (1 / 2 : ℂ)) • (D 1 y + Complex.I • D Complex.I y)) := by
    funext y
    dsimp only [ψ, D]
    rw [reflected_test_fderiv hρ, reflected_test_fderiv hρ]
    have hreal (r : ℝ) : (r : ℂ) • F y = r • F y :=
      IsScalarTower.algebraMap_smul ℂ r (F y)
    simp only [Complex.ofReal_neg]
    rw [← hreal, ← hreal]
    module
  have hIi : Integrable (fun y => Complex.I • D Complex.I y) := by
    change Integrable (Complex.I • D Complex.I)
    exact (hDi Complex.I).smul Complex.I
  rw [htest, integral_smul, integral_add (hDi 1) hIi,
    integral_smul] at hw
  have hsum : (∫ y, D 1 y) + Complex.I • (∫ y, D Complex.I y) = 0 :=
    (smul_eq_zero.mp hw).resolve_left (by norm_num)
  have hcr := congrArg (fun v : V => Complex.I • v) hsum
  simp only [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, smul_zero] at hcr
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨(hc.hasFDerivAt_convolution_right
    (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (μ := (volume : Measure ℂ))
    hF.locallyIntegrable (hρ.of_le (by simp)) z).differentiableAt, ?_⟩
  rw [convolution_fderiv_apply hF hρ hc, convolution_fderiv_apply hF hρ hc]
  exact (eq_of_sub_eq_zero (by simpa only [D, sub_eq_add_neg] using hcr)).symm

private def weakHolomorphicBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

private theorem analyticOnNhd_of_continuous_of_weak_dbar_zero
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F : ℂ → V} (hF : Continuous F)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ y : ℂ, (((fderiv ℝ φ y (1 : ℂ) : ℂ) +
        Complex.I * (fderiv ℝ φ y Complex.I : ℂ)) / 2) • F y) = 0) :
    AnalyticOnNhd ℂ F Ω := by
  have hlim : Tendsto (fun n => (weakHolomorphicBump n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv := normed_bump_convolution_tendstoLocallyUniformly weakHolomorphicBump hlim hF
  apply DifferentiableOn.analyticOnNhd _ hΩ
  intro p hp
  obtain ⟨r, hr, hrΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hp)
  have hdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ
        ((weakHolomorphicBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F)
        (ball p (r / 2)) := by
    filter_upwards [hlim.eventually (gt_mem_nhds (half_pos hr))] with n hn
    intro z hz
    rw [← convolution_flip]
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_convolution_of_weak_dbar_zero hF hweak
      (weakHolomorphicBump n).contDiff_normed (weakHolomorphicBump n).hasCompactSupport_normed z
    intro y hy
    apply hrΩ
    have hyz : dist y z ≤ (weakHolomorphicBump n).rOut := by
      rw [(weakHolomorphicBump n).tsupport_normed_eq] at hy
      simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using hy
    have hzp : dist z p < r / 2 := hz
    exact (dist_triangle y z p).trans (by linarith)
  have hFdiff : DifferentiableOn ℂ F (ball p (r / 2)) :=
    ((tendstoLocallyUniformlyOn_univ.mpr hconv).mono (subset_univ _)).differentiableOn
      hdiff isOpen_ball
  exact (hFdiff.differentiableAt (ball_mem_nhds p (half_pos hr))).differentiableWithinAt

/-- A continuous representative whose weak `∂bar` vanishes is analytic on the
original open set. The real test-function normalization is the literal one used
by the Cauchy integral weak equation. No Sobolev or Lipschitz premise is needed. -/
theorem analyticOnNhd_of_continuousOn_of_integral_realTestDbar_smul_eq_zero
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F : ℂ → V} (hF : ContinuousOn F Ω)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ y : ℂ, (((fderiv ℝ φ y (1 : ℂ) : ℂ) +
        Complex.I * (fderiv ℝ φ y Complex.I : ℂ)) / 2) • F y) = 0) :
    AnalyticOnNhd ℂ F Ω := by
  intro p hp
  obtain ⟨r, hr, hrΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hp)
  let χ : ContDiffBump p := {
    rIn := r / 2
    rOut := r
    rIn_pos := half_pos hr
    rIn_lt_rOut := by linarith }
  have hχs : tsupport χ ⊆ Ω := by
    rw [χ.tsupport_eq]
    exact hrΩ
  let G : ℂ → V := fun z => χ z • F z
  have hG : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z ∈ Ω
    · exact χ.continuous.continuousAt.smul ((hF z hz).continuousAt (hΩ.mem_nhds hz))
    · have hn : z ∉ tsupport χ := fun hh => hz (hχs hh)
      have heq : G =ᶠ[𝓝 z] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
        simp only [G, hy, zero_smul, Pi.zero_apply]
      exact continuousAt_const.congr heq.symm
  have hinner : ball p (r / 2) ⊆ Ω :=
    (ball_subset_ball (by linarith : r / 2 ≤ r)).trans (ball_subset_closedBall.trans hrΩ)
  have hGF : EqOn G F (ball p (r / 2)) := by
    intro z hz
    have hχ : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hz)
    simp only [G, hχ, one_smul]
  have hGweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball p (r / 2) →
      (∫ y : ℂ, (((fderiv ℝ φ y (1 : ℂ) : ℂ) +
        Complex.I * (fderiv ℝ φ y Complex.I : ℂ)) / 2) • G y) = 0 := by
    intro φ hφ hc hs
    calc
      _ = ∫ y : ℂ, (((fderiv ℝ φ y (1 : ℂ) : ℂ) +
          Complex.I * (fderiv ℝ φ y Complex.I : ℂ)) / 2) • F y := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          dsimp only
          by_cases hy : y ∈ ball p (r / 2)
          · rw [hGF hy]
          · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hy (hs hh))]
            simp
      _ = 0 := hweak φ hφ hc (hs.trans hinner)
  have hGa := analyticOnNhd_of_continuous_of_weak_dbar_zero isOpen_ball hG hGweak
  exact (hGa p (mem_ball_self (half_pos hr))).congr
    (hGF.eventuallyEq_of_mem (ball_mem_nhds p (half_pos hr)))

end DifferentialGeometry.Analysis
