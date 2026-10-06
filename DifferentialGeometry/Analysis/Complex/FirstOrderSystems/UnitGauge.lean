import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

private theorem fderiv_complex_clm_apply
    {P : ℂ → V →L[ℂ] V} {f : ℂ → V} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hf : DifferentiableAt ℝ f z) (v : ℂ) :
    fderiv ℝ (fun w => P w (f w)) z v =
      P z (fderiv ℝ f z v) + (fderiv ℝ P z v) (f z) := by
  let r : (V →L[ℂ] V) →L[ℝ] (V →L[ℝ] V) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ V V ℝ ℝ).toContinuousLinearMap
  have hPr : HasFDerivAt (fun w => (P w).restrictScalars ℝ)
      (r.comp (fderiv ℝ P z)) z :=
    r.hasFDerivAt.comp z hP.hasFDerivAt
  exact congrArg (fun L : ℂ →L[ℝ] V => L v) (hPr.clm_apply hf.hasFDerivAt).fderiv

private theorem dbar_complex_clm_apply
    {P : ℂ → V →L[ℂ] V} {f : ℂ → V} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hf : DifferentiableAt ℝ f z) :
    (1 / 2 : ℂ) •
        (fderiv ℝ (fun w => P w (f w)) z (1 : ℂ) +
          Complex.I • fderiv ℝ (fun w => P w (f w)) z Complex.I) =
      ((1 / 2 : ℂ) •
        (fderiv ℝ P z (1 : ℂ) + Complex.I • fderiv ℝ P z Complex.I)) (f z) +
      P z ((1 / 2 : ℂ) •
        (fderiv ℝ f z (1 : ℂ) + Complex.I • fderiv ℝ f z Complex.I)) := by
  simp only [fderiv_complex_clm_apply hP hf, _root_.smul_apply,
    _root_.add_apply, map_add, map_smul, smul_add]
  abel

/-- A pointwise-unit gauge for a complex first-order system makes the same
inverse-gauged section analytic. The two differential equations are explicit
inputs; this theorem does not construct a gauge or assert a nonzero germ. -/
theorem analyticOnNhd_inverse_gauge_apply [CompleteSpace V]
    {S : Set ℂ} (hS : IsOpen S)
    (P A : ℂ → V →L[ℂ] V) (ξ : ℂ → V)
    (hP : ContDiffOn ℝ 1 P S) (hξ : ContDiffOn ℝ 1 ξ S)
    (hunit : ∀ z ∈ S, IsUnit (P z))
    (hPDE : ∀ z ∈ S,
      (1 / 2 : ℂ) •
          (fderiv ℝ P z (1 : ℂ) + Complex.I • fderiv ℝ P z Complex.I) =
        A z * P z)
    (hξDE : ∀ z ∈ S,
      (1 / 2 : ℂ) •
          (fderiv ℝ ξ z (1 : ℂ) + Complex.I • fderiv ℝ ξ z Complex.I) =
        A z (ξ z)) :
    AnalyticOnNhd ℂ (fun z => (Ring.inverse (P z)) (ξ z)) S ∧
      (∀ z ∈ S, ξ z = P z ((Ring.inverse (P z)) (ξ z))) ∧
      (∀ z ∈ S, (Ring.inverse (P z)) (ξ z) = 0 ↔ ξ z = 0) := by
  let F : ℂ → V := fun z => (Ring.inverse (P z)) (ξ z)
  have hPd (z : ℂ) (hz : z ∈ S) : DifferentiableAt ℝ P z :=
    hP.differentiableOn_one.differentiableAt (hS.mem_nhds hz)
  have hξd (z : ℂ) (hz : z ∈ S) : DifferentiableAt ℝ ξ z :=
    hξ.differentiableOn_one.differentiableAt (hS.mem_nhds hz)
  have hFd (z : ℂ) (hz : z ∈ S) : DifferentiableAt ℝ F z := by
    let r : (V →L[ℂ] V) →L[ℝ] (V →L[ℝ] V) :=
      (ContinuousLinearMap.restrictScalarsIsometry ℂ V V ℝ ℝ).toContinuousLinearMap
    have hi := (hPd z hz).inverse (hunit z hz)
    exact (r.differentiableAt.comp z hi).clm_apply (hξd z hz)
  have hfactor (z : ℂ) (hz : z ∈ S) : ξ z = P z (F z) := by
    change ξ z = (P z * Ring.inverse (P z)) (ξ z)
    rw [Ring.mul_inverse_cancel _ (hunit z hz)]
    rfl
  have hhol : DifferentiableOn ℂ F S := by
    intro z hz
    have heq : (fun w => P w (F w)) =ᶠ[𝓝 z] ξ := by
      filter_upwards [hS.mem_nhds hz] with w hw
      exact (hfactor w hw).symm
    have hd := dbar_complex_clm_apply (hPd z hz) (hFd z hz)
    simp only [heq.fderiv_eq, hξDE z hz, hPDE z hz] at hd
    have hAP : (A z * P z) (F z) = A z (ξ z) := by
      change A z (P z (F z)) = A z (ξ z)
      rw [← hfactor z hz]
    rw [hAP] at hd
    have hPzero : P z ((1 / 2 : ℂ) •
        (fderiv ℝ F z (1 : ℂ) + Complex.I • fderiv ℝ F z Complex.I)) = 0 :=
      add_left_cancel (hd.symm.trans (add_zero _).symm)
    have hcancel (v : V) : (Ring.inverse (P z)) (P z v) = v := by
      change (Ring.inverse (P z) * P z) v = v
      rw [Ring.inverse_mul_cancel _ (hunit z hz)]
      rfl
    have hzero := congrArg (fun v : V => (Ring.inverse (P z) : V →L[ℂ] V) v) hPzero
    rw [hcancel, map_zero] at hzero
    have hsum := congrArg (fun v : V => (2 : ℂ) • v) hzero
    have htwo : (2 : ℂ) * (1 / 2 : ℂ) = 1 := by norm_num
    simp only [smul_smul, htwo, one_smul, smul_zero] at hsum
    have hcr0 := congrArg (fun v : V => Complex.I • v) hsum
    simp only [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, smul_zero] at hcr0
    have hcr : fderiv ℝ F z Complex.I = Complex.I • fderiv ℝ F z (1 : ℂ) :=
      (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hcr0)).symm
    exact (differentiableAt_complex_iff_differentiableAt_real.mpr
      ⟨hFd z hz, hcr⟩).differentiableWithinAt
  refine ⟨hhol.analyticOnNhd hS, hfactor, ?_⟩
  intro z hz
  constructor
  · intro hzero
    calc
      ξ z = P z (F z) := hfactor z hz
      _ = P z 0 := congrArg (P z) hzero
      _ = 0 := map_zero _
  · intro hzero
    simp only [hzero, map_zero]

end DifferentialGeometry.Analysis
