import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Module

set_option autoImplicit false
noncomputable section

open Set Filter Metric MeasureTheory Function
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

private theorem convolution_fderiv_apply
    {F : ℂ → V} (hF : LocallyIntegrable F volume) {ρ : ℂ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (z v : ℂ) :
    fderiv ℝ (F ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] ρ) z v =
      ∫ y : ℂ, (fderiv ℝ ρ (z - y) v) • F y := by
  have hd := hc.hasFDerivAt_convolution_right
    (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (μ := (volume : Measure ℂ))
    hF (hρ.of_le (by simp)) z
  rw [hd.fderiv, convolution_precompR_apply
    (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip) hF
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

/-- A smooth compact convolution commutes with the literal weak `∂bar` equation
where the translated kernel support remains in the original weak-equation domain.
Both inputs need only be locally integrable; the right-hand side need not be continuous. -/
theorem convolution_dbar_of_integral_realTestDbar_smul
    {Ω : Set ℂ} {F G : ℂ → V}
    (hF : LocallyIntegrable F volume) (hG : LocallyIntegrable G volume)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ y : ℂ, (((fderiv ℝ φ y (1 : ℂ) : ℂ) +
        Complex.I * (fderiv ℝ φ y Complex.I : ℂ)) / 2) • F y) =
        -(∫ y : ℂ, φ y • G y))
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (z : ℂ)
    (hsupport : ∀ y, z - y ∈ tsupport ρ → y ∈ Ω) :
    ConvolutionExistsAt ρ G z (ContinuousLinearMap.lsmul ℝ ℝ) volume ∧
      (1 / 2 : ℂ) •
        (fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) z 1 +
          Complex.I • fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) z Complex.I) =
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) z := by
  refine ⟨hc.convolutionExists_left _ hρ.continuous hG z, ?_⟩
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
    apply hF.integrable_smul_left_of_hasCompactSupport
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
  rw [htest, integral_smul, integral_add (hDi 1) hIi, integral_smul] at hw
  have hh := congrArg Neg.neg hw
  simp only [neg_smul, neg_neg] at hh
  rw [← convolution_flip (g := F), ← convolution_flip (g := G)]
  rw [convolution_fderiv_apply hF hρ hc, convolution_fderiv_apply hF hρ hc]
  exact hh

/-- The exact `∂bar` equation for normalized bump mollifications on a buffered
inner ball. This applies unchanged to operator-valued gauges. -/
theorem normed_bump_convolution_dbar_eq_on_ball
    {F G : ℂ → V} (hF : LocallyIntegrable F volume) (hG : LocallyIntegrable G volume)
    {c : ℂ} {r R : ℝ}
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball c R →
      (∫ y : ℂ, (((fderiv ℝ φ y (1 : ℂ) : ℂ) +
        Complex.I * (fderiv ℝ φ y Complex.I : ℂ)) / 2) • F y) =
        -(∫ y : ℂ, φ y • G y))
    (ρ : ContDiffBump (0 : ℂ)) (hbuffer : r + ρ.rOut ≤ R) :
    ∀ z ∈ ball c r,
      (1 / 2 : ℂ) •
        (fderiv ℝ (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) z 1 +
          Complex.I • fderiv ℝ
            (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) z Complex.I) =
        (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) z := by
  intro z hz
  apply (convolution_dbar_of_integral_realTestDbar_smul hF hG hweak
    ρ.contDiff_normed ρ.hasCompactSupport_normed z ?_).2
  intro y hy
  have hyz : dist y z ≤ ρ.rOut := by
    rw [ρ.tsupport_normed_eq] at hy
    simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using hy
  have hzc : dist z c < r := hz
  exact (dist_triangle y z c).trans_lt (by linarith)

end DifferentialGeometry.Analysis
