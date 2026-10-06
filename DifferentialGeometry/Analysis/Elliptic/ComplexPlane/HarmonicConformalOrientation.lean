/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Conformal.InnerProduct
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A uniform analytic orientation for a harmonic planar map

A harmonic map that is conformal near one point of a connected open planar
set is analytic, or its output conjugate is analytic, throughout that set.
The argument uses the analytic complex partials of its two real coordinates.
-/

open Set Filter InnerProductSpace Complex
open scoped Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Analysis

private theorem complex_partial_re_im_identities {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    let α : ℂ := (fderiv ℝ (reCLM ∘ f) z 1 : ℂ) -
      I * (fderiv ℝ (reCLM ∘ f) z I : ℂ)
    let β : ℂ := (fderiv ℝ (imCLM ∘ f) z 1 : ℂ) -
      I * (fderiv ℝ (imCLM ∘ f) z I : ℂ)
    α + I * β = fderiv ℝ f z 1 - I * fderiv ℝ f z I ∧
      α - I * β = conjCLE (fderiv ℝ f z 1 + I * fderiv ℝ f z I) := by
  have hRe : fderiv ℝ (reCLM ∘ f) z = reCLM.comp (fderiv ℝ f z) :=
    (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  have hIm : fderiv ℝ (imCLM ∘ f) z = imCLM.comp (fderiv ℝ f z) :=
    (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  dsimp only
  simp only [hRe, hIm, ContinuousLinearMap.comp_apply, reCLM_apply, imCLM_apply]
  constructor <;> apply Complex.ext <;> simp <;> ring

private theorem conformal_partial_product_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : ConformalAt f z) :
    (fderiv ℝ f z 1 - I * fderiv ℝ f z I) *
      conjCLE (fderiv ℝ f z 1 + I * fderiv ℝ f z I) = 0 := by
  obtain ⟨c, _, hc⟩ := conformalAt_iff'.mp hf
  have h11 : ‖fderiv ℝ f z 1‖ ^ 2 = c := by
    simpa only [real_inner_self_eq_norm_sq, norm_one, one_pow, mul_one] using hc (1 : ℂ) 1
  have hII : ‖fderiv ℝ f z I‖ ^ 2 = c := by
    simpa only [real_inner_self_eq_norm_sq, norm_I, one_pow, mul_one] using hc I I
  have h1I := hc 1 I
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply] at h1I
  rw [Complex.sq_norm, Complex.normSq_apply] at h11 hII
  apply Complex.ext <;> simp <;> nlinarith [h11, hII, h1I]

/-- A conformal patch fixes one analytic orientation on a connected harmonic domain. -/
theorem analyticOnNhd_or_conj_of_harmonicOnNhd_of_eventually_conformalAt
    {f : ℂ → ℂ} {D : Set ℂ} {x : ℂ}
    (hD : IsOpen D) (hconn : IsPreconnected D)
    (hf : InnerProductSpace.HarmonicOnNhd f D) (hx : x ∈ D)
    (hconf : ∀ᶠ z in 𝓝 x, ConformalAt f z) :
    AnalyticOnNhd ℂ f D ∨
      AnalyticOnNhd ℂ (fun z => Complex.conjCLE (f z)) D := by
  let α : ℂ → ℂ := fun z => (fderiv ℝ (reCLM ∘ f) z 1 : ℂ) -
    I * (fderiv ℝ (reCLM ∘ f) z I : ℂ)
  let β : ℂ → ℂ := fun z => (fderiv ℝ (imCLM ∘ f) z 1 : ℂ) -
    I * (fderiv ℝ (imCLM ∘ f) z I : ℂ)
  let A : ℂ → ℂ := fun z => α z + I * β z
  let B : ℂ → ℂ := fun z => α z - I * β z
  have hα : AnalyticOnNhd ℂ α D := by
    intro z hz
    exact HarmonicAt.analyticAt_complex_partial ((hf.comp_CLM reCLM) z hz)
  have hβ : AnalyticOnNhd ℂ β D := by
    intro z hz
    exact HarmonicAt.analyticAt_complex_partial ((hf.comp_CLM imCLM) z hz)
  have hA : AnalyticOnNhd ℂ A D := fun z hz =>
    (hα z hz).add (analyticAt_const.mul (hβ z hz))
  have hB : AnalyticOnNhd ℂ B D := fun z hz =>
    (hα z hz).sub (analyticAt_const.mul (hβ z hz))
  have hcols (z : ℂ) (hz : z ∈ D) :
      A z = fderiv ℝ f z 1 - I * fderiv ℝ f z I ∧
        B z = conjCLE (fderiv ℝ f z 1 + I * fderiv ℝ f z I) :=
    complex_partial_re_im_identities ((hf z hz).1.differentiableAt two_ne_zero)
  have hnear : (fun z => A z * B z) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hconf, hD.mem_nhds hx] with z hcz hz
    change A z * B z = 0
    rw [(hcols z hz).1, (hcols z hz).2]
    exact conformal_partial_product_zero hcz
  have hprod : ∀ z ∈ D, A z * B z = 0 := by
    have hzero := (hA.mul hB).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hconn hx hnear
    intro z hz
    exact hzero hz
  rcases hA.eq_zero_or_eq_zero_of_mul_eq_zero hB hprod hconn with hAz | hBz
  · right
    apply DifferentiableOn.analyticOnNhd _ hD
    intro z hz
    have hdf : DifferentiableAt ℝ f z := (hf z hz).1.differentiableAt two_ne_zero
    refine (differentiableAt_complex_iff_differentiableAt_real.mpr
      ⟨conjCLE.differentiableAt.comp z hdf, ?_⟩).differentiableWithinAt
    have hdconj : fderiv ℝ (fun w => conjCLE (f w)) z =
        (conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z) :=
      (conjCLE.hasFDerivAt.comp z hdf.hasFDerivAt).fderiv
    change fderiv ℝ (fun w => conjCLE (f w)) z I =
      I • fderiv ℝ (fun w => conjCLE (f w)) z 1
    rw [hdconj]
    change conjCLE (fderiv ℝ f z I) = I * conjCLE (fderiv ℝ f z 1)
    have hzero : fderiv ℝ f z 1 - I * fderiv ℝ f z I = 0 :=
      (hcols z hz).1.symm.trans (hAz z hz)
    have hre := congrArg Complex.re hzero
    have him := congrArg Complex.im hzero
    apply Complex.ext <;> simp at hre him ⊢ <;> linarith
  · left
    apply DifferentiableOn.analyticOnNhd _ hD
    intro z hz
    have hdf : DifferentiableAt ℝ f z := (hf z hz).1.differentiableAt two_ne_zero
    refine (differentiableAt_complex_iff_differentiableAt_real.mpr
      ⟨hdf, ?_⟩).differentiableWithinAt
    have hzero : conjCLE (fderiv ℝ f z 1 + I * fderiv ℝ f z I) = 0 :=
      (hcols z hz).2.symm.trans (hBz z hz)
    have hsum : fderiv ℝ f z 1 + I * fderiv ℝ f z I = 0 :=
      conjCLE.injective (hzero.trans (map_zero conjCLE).symm)
    have hre := congrArg Complex.re hsum
    have him := congrArg Complex.im hsum
    change fderiv ℝ f z I = I * fderiv ℝ f z 1
    apply Complex.ext <;> simp at hre him ⊢ <;> linarith

end DifferentialGeometry.Analysis
