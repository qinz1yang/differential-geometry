import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM



open Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem second_deriv_nonneg_of_isLocalMin {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hn : deriv (deriv f) x < 0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmin, hmax] with y hy hz
    exact le_antisymm hz hy
  have hd : deriv f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [heq.deriv] with y hy
    simpa only [deriv_const] using hy
  have hdd : deriv (deriv f) x = 0 := by
    simpa only [deriv_const] using hd.deriv_eq
  linarith

theorem secondDirectional_nonneg_of_localMin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hmin : IsLocalMin f z) (v : E) :
    0 ≤ fderiv ℝ (fun q => fderiv ℝ f q v) z v := by
  let line : ℝ → E := fun t => z + t • v
  let φ : ℝ → ℝ := f ∘ line
  have hl (t : ℝ) : HasDerivAt line v t := by
    simpa [line] using ((hasDerivAt_id t).smul_const v).const_add z
  have hl0 : line 0 = z := by simp [line]
  have hm : IsLocalMin φ 0 := by
    have h : IsLocalMin f (line 0) := by rwa [hl0]
    exact h.comp_continuous (hl 0).continuousAt
  have hfd := hf.differentiableAt (by norm_num)
  have hfirst : HasDerivAt φ 0 0 := by
    have h := hfd.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) (hl 0) hl0.symm
    simpa only [hmin.fderiv_eq_zero, _root_.zero_apply] using h
  have hpartial : DifferentiableAt ℝ (fun q => fderiv ℝ f q v) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hnear : deriv φ =ᶠ[𝓝 0] (fun t => fderiv ℝ f (line t) v) := by
    have hreg : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 f (line t) := by
      have ht : Tendsto line (𝓝 0) (𝓝 z) := by
        have ht := (hl 0).continuousAt
        change Tendsto line (𝓝 0) (𝓝 (line 0)) at ht
        rwa [hl0] at ht
      exact ht.eventually (hf.eventually (by norm_num))
    filter_upwards [hreg] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  have hsecond : HasDerivAt (deriv φ)
      (fderiv ℝ (fun q => fderiv ℝ f q v) z v) 0 :=
    (hpartial.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) (hl 0) hl0.symm).congr_of_eventuallyEq hnear
  rw [← hsecond.deriv]
  exact second_deriv_nonneg_of_isLocalMin hm hfirst.continuousAt

end DifferentialGeometry.Analysis
