import DifferentialGeometry.Analysis.Integration.Integral.CompactSupport
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The real-derivative formula for the complex anti-holomorphic derivative of a section. -/
def complexDbar (f : ℂ → V) (z : ℂ) : V :=
  (1 / 2 : ℂ) • (fderiv ℝ f z 1 + Complex.I • fderiv ℝ f z Complex.I)

/-- Compatibility with the literal real-test convention in the bounded Cauchy
weak equation and the continuous weak-holomorphic supplier. -/
theorem complexDbar_ofReal {φ : ℂ → ℝ} {z : ℂ}
    (hφ : DifferentiableAt ℝ φ z) :
    complexDbar (fun w => (φ w : ℂ)) z =
      ((fderiv ℝ φ z 1 : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2 := by
  have hh := (Complex.ofRealCLM.hasFDerivAt.comp z hφ.hasFDerivAt).fderiv
  have hd (t : ℂ) : fderiv ℝ (fun w => (φ w : ℂ)) z t = (fderiv ℝ φ z t : ℂ) :=
    congrArg (fun L : ℂ →L[ℝ] ℂ => L t) hh
  simp only [complexDbar, hd, smul_eq_mul, div_eq_mul_inv]
  ring

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

private theorem complexDbar_clm_apply
    {P : ℂ → V →L[ℂ] V} {f : ℂ → V} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hf : DifferentiableAt ℝ f z) :
    complexDbar (fun w => P w (f w)) z =
      complexDbar P z (f z) + P z (complexDbar f z) := by
  simp only [complexDbar, fderiv_complex_clm_apply hP hf, _root_.smul_apply,
    _root_.add_apply, map_add, map_smul, smul_add]
  abel

variable [CompleteSpace V]

/-- An approximate gauge has an exact inverse-section residual. Only the smooth
approximating gauge is differentiated; the limiting gauge need not be differentiable. -/
theorem complexDbar_inverse_gauge_residual
    {Q A : ℂ → V →L[ℂ] V} {ξ : ℂ → V} {z : ℂ}
    (hQ : DifferentiableAt ℝ Q z) (hξ : DifferentiableAt ℝ ξ z)
    (hunit : IsUnit (Q z)) (hξeq : complexDbar ξ z = A z (ξ z)) :
    complexDbar (fun w => Ring.inverse (Q w) (ξ w)) z =
      Ring.inverse (Q z)
        ((A z * Q z - complexDbar Q z) (Ring.inverse (Q z) (ξ z))) := by
  let F : ℂ → V := fun w => Ring.inverse (Q w) (ξ w)
  let r : (V →L[ℂ] V) →L[ℝ] (V →L[ℝ] V) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ V V ℝ ℝ).toContinuousLinearMap
  have hFd : DifferentiableAt ℝ F z :=
    (r.differentiableAt.comp z (hQ.inverse hunit)).clm_apply hξ
  have hunitN : ∀ᶠ w in 𝓝 z, IsUnit (Q w) :=
    hQ.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
  have hfactor : (fun w => Q w (F w)) =ᶠ[𝓝 z] ξ := by
    filter_upwards [hunitN] with w hw
    change (Q w * Ring.inverse (Q w)) (ξ w) = ξ w
    rw [Ring.mul_inverse_cancel _ hw]
    rfl
  have hprod := complexDbar_clm_apply hQ hFd
  have hde : complexDbar (fun w => Q w (F w)) z = complexDbar ξ z := by
    simp only [complexDbar, hfactor.fderiv_eq]
  rw [hde, hξeq] at hprod
  have hfactor0 : Q z (F z) = ξ z := by
    change (Q z * Ring.inverse (Q z)) (ξ z) = ξ z
    rw [Ring.mul_inverse_cancel _ hunit]
    rfl
  have hres : Q z (complexDbar F z) =
      (A z * Q z - complexDbar Q z) (F z) := by
    change Q z (complexDbar F z) = A z (Q z (F z)) - complexDbar Q z (F z)
    rw [hfactor0]
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hprod.symm)
  have hcancel (v : V) : Ring.inverse (Q z) (Q z v) = v := by
    change (Ring.inverse (Q z) * Q z) v = v
    rw [Ring.inverse_mul_cancel _ hunit]
    rfl
  have hh := congrArg (fun v : V => Ring.inverse (Q z) v) hres
  rw [hcancel] at hh
  exact hh

/-- Uniform inverse control converts the coefficient residual into a differential
residual for the literal inverse-gauged section. -/
theorem norm_complexDbar_inverse_gauge_le
    {Q A : ℂ → V →L[ℂ] V} {ξ : ℂ → V} {z : ℂ}
    (hQ : DifferentiableAt ℝ Q z) (hξ : DifferentiableAt ℝ ξ z)
    (hunit : IsUnit (Q z)) (hξeq : complexDbar ξ z = A z (ξ z))
    {L M : ℝ} (hL : 0 ≤ L)
    (hinv : ‖Ring.inverse (Q z)‖ ≤ L) (hval : ‖ξ z‖ ≤ M) :
    ‖complexDbar (fun w => Ring.inverse (Q w) (ξ w)) z‖ ≤
      L ^ 2 * M * ‖A z * Q z - complexDbar Q z‖ := by
  rw [complexDbar_inverse_gauge_residual hQ hξ hunit hξeq]
  calc
    _ ≤ ‖Ring.inverse (Q z)‖ *
        ‖(A z * Q z - complexDbar Q z) (Ring.inverse (Q z) (ξ z))‖ :=
      (Ring.inverse (Q z)).le_opNorm _
    _ ≤ L * (‖A z * Q z - complexDbar Q z‖ * (L * M)) := by
      apply mul_le_mul hinv _ (norm_nonneg _) hL
      exact ((A z * Q z - complexDbar Q z).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left
          (((Ring.inverse (Q z)).le_opNorm _).trans
            (mul_le_mul hinv hval (norm_nonneg _) hL)) (norm_nonneg _))
    _ = _ := by ring

private theorem contDiffOn_inverse_gauge
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {Q : ℂ → V →L[ℂ] V} {ξ : ℂ → V}
    (hQ : ContDiffOn ℝ 1 Q Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hunit : ∀ z ∈ Ω, IsUnit (Q z)) :
    ContDiffOn ℝ 1 (fun z => Ring.inverse (Q z) (ξ z)) Ω := by
  let r : (V →L[ℂ] V) →L[ℝ] (V →L[ℝ] V) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ V V ℝ ℝ).toContinuousLinearMap
  intro z hz
  obtain ⟨u, hu⟩ := hunit z hz
  have hi : ContDiffAt ℝ 1 (fun w => Ring.inverse (Q w)) z := by
    have hInv : ContDiffAt ℝ 1 Ring.inverse (Q z) := by
      rw [← hu]
      exact contDiffAt_ringInverse ℝ u
    exact hInv.comp z (hQ.contDiffAt (hΩ.mem_nhds hz))
  exact ((r.contDiff.contDiffAt.comp z hi).clm_apply
    (hξ.contDiffAt (hΩ.mem_nhds hz))).contDiffWithinAt

omit [CompleteSpace V] in
private theorem integrable_and_integral_complexDbar_smul
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → V}
    (hf : ContDiffOn ℝ 1 f Ω) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun z => complexDbar φ z • f z) ∧
      Integrable (fun z => φ z • complexDbar f z) ∧
      (∫ z, complexDbar φ z • f z) = -(∫ z, φ z • complexDbar f z) := by
  have hfi := hf.continuousOn.locallyIntegrableOn (μ := volume) hΩ.measurableSet
  have hDi (t : ℂ) : LocallyIntegrableOn (fun z => fderiv ℝ f z t) Ω volume :=
    ContinuousOn.locallyIntegrableOn
      ((hf.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const)
      hΩ.measurableSet
  have hleft (t : ℂ) : Integrable (fun z => fderiv ℝ φ z t • f z) :=
    hfi.integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hc.fderiv_apply (𝕜 := ℝ) t) ((tsupport_fderiv_apply_subset ℝ t).trans hs)
  have hright (t : ℂ) : Integrable (fun z => φ z • fderiv ℝ f z t) :=
    (hDi t).integrable_smul_left_of_hasCompactSupport hφ.continuous hc hs
  have hbase : Integrable (fun z => φ z • f z) :=
    hfi.integrable_smul_left_of_hasCompactSupport hφ.continuous hc hs
  have hibp (t : ℂ) : (∫ z, φ z • fderiv ℝ f z t) =
      -(∫ z, fderiv ℝ φ z t • f z) :=
    integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (hleft t) (hright t) hbase
      (fun z _ => (hφ.differentiable one_ne_zero) z)
      (fun z hz => hf.differentiableOn_one.differentiableAt (hΩ.mem_nhds (hs hz)))
  have hleftEq : (fun z => complexDbar φ z • f z) =
      (fun z => (1 / 2 : ℂ) • (fderiv ℝ φ z 1 • f z +
        Complex.I • (fderiv ℝ φ z Complex.I • f z))) := by
    funext z
    simp only [complexDbar, smul_add, add_smul, smul_smul, smul_eq_mul, mul_add]
  have hrightEq : (fun z => φ z • complexDbar f z) =
      (fun z => (1 / 2 : ℂ) • (φ z • fderiv ℝ f z 1 +
        Complex.I • (φ z • fderiv ℝ f z Complex.I))) := by
    funext z
    rw [complexDbar, smul_comm (φ z) (1 / 2 : ℂ), smul_add,
      smul_comm (φ z) Complex.I]
  have hleftD : Integrable (fun z => complexDbar φ z • f z) := by
    rw [hleftEq]
    exact ((hleft 1).add ((hleft Complex.I).smul Complex.I)).smul (1 / 2 : ℂ)
  have hrightD : Integrable (fun z => φ z • complexDbar f z) := by
    rw [hrightEq]
    exact ((hright 1).add ((hright Complex.I).smul Complex.I)).smul (1 / 2 : ℂ)
  refine ⟨hleftD, hrightD, ?_⟩
  have heq : (∫ z, φ z • complexDbar f z) =
      -(∫ z, complexDbar φ z • f z) := by
    have hrightI : Integrable
        (fun z => Complex.I • (φ z • fderiv ℝ f z Complex.I)) :=
      (hright Complex.I).smul Complex.I
    have hleftI : Integrable
        (fun z => Complex.I • (fderiv ℝ φ z Complex.I • f z)) :=
      (hleft Complex.I).smul Complex.I
    rw [hrightEq, hleftEq, integral_smul,
      integral_add (hright 1) hrightI, integral_smul,
      integral_smul, integral_add (hleft 1) hleftI, integral_smul,
      hibp 1, hibp Complex.I]
    simp only [smul_add, smul_neg, neg_add]
  have hh := congrArg Neg.neg heq
  simpa only [neg_neg] using hh.symm

/-- Smooth inverse gauges pass to a weakly holomorphic section when their actual
coefficient residual tends to zero in the weighted local `L¹` norm. The two limit
hypotheses are explicit mollification obligations: no regularity or weak product
rule for the limiting gauge is assumed. -/
theorem integral_complexDbar_smul_inverse_gauge_eq_zero_of_approximation
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (P A : ℂ → V →L[ℂ] V) (ξ : ℂ → V) (Q : ℕ → ℂ → V →L[ℂ] V)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hQ : ∀ n, ContDiffOn ℝ 1 (Q n) Ω)
    (hunit : ∀ n z, z ∈ Ω → IsUnit (Q n z))
    (hξeq : ∀ z ∈ Ω, complexDbar ξ z = A z (ξ z))
    {L M : ℝ} (hL : 0 ≤ L)
    (hinv : ∀ n z, z ∈ Ω → ‖Ring.inverse (Q n z)‖ ≤ L)
    (hval : ∀ z ∈ Ω, ‖ξ z‖ ≤ M)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω)
    (hF : Integrable (fun z => complexDbar φ z • Ring.inverse (P z) (ξ z)))
    (happrox : Tendsto (fun n => ∫ z, ‖complexDbar φ z •
      (Ring.inverse (Q n z) (ξ z) - Ring.inverse (P z) (ξ z))‖) atTop (𝓝 0))
    (hresInt : ∀ n, Integrable (fun z =>
      ‖φ z‖ * ‖A z * Q n z - complexDbar (Q n) z‖))
    (hresLim : Tendsto (fun n => ∫ z,
      ‖φ z‖ * ‖A z * Q n z - complexDbar (Q n) z‖) atTop (𝓝 0)) :
    (∫ z, complexDbar φ z • Ring.inverse (P z) (ξ z)) = 0 := by
  let F : ℂ → V := fun z => Ring.inverse (P z) (ξ z)
  let Fₙ : ℕ → ℂ → V := fun n z => Ring.inverse (Q n z) (ξ z)
  have hFn (n : ℕ) : ContDiffOn ℝ 1 (Fₙ n) Ω :=
    contDiffOn_inverse_gauge hΩ (hQ n) hξ (hunit n)
  have hInt (n : ℕ) := integrable_and_integral_complexDbar_smul hΩ (hFn n) hφ hc hs
  have hnorm (n : ℕ) : ‖∫ z, φ z • complexDbar (Fₙ n) z‖ ≤
      (L ^ 2 * M) * (∫ z, ‖φ z‖ * ‖A z * Q n z - complexDbar (Q n) z‖) := by
    calc
      _ ≤ ∫ z, ‖φ z • complexDbar (Fₙ n) z‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, (L ^ 2 * M) *
          (‖φ z‖ * ‖A z * Q n z - complexDbar (Q n) z‖) := by
        apply integral_mono_ae (hInt n).2.1.norm ((hresInt n).const_mul _)
        filter_upwards with z
        by_cases hz : z ∈ Ω
        · rw [norm_smul]
          calc
            _ ≤ ‖φ z‖ * (L ^ 2 * M * ‖A z * Q n z - complexDbar (Q n) z‖) :=
              mul_le_mul_of_nonneg_left
                (norm_complexDbar_inverse_gauge_le
                  ((hQ n).differentiableOn_one.differentiableAt (hΩ.mem_nhds hz))
                  (hξ.differentiableOn_one.differentiableAt (hΩ.mem_nhds hz))
                  (hunit n z hz) (hξeq z hz) hL (hinv n z hz) (hval z hz))
                (norm_nonneg _)
            _ = _ := by ring
        · have hφz : φ z = 0 := by
            by_contra hn
            exact hz (hs (subset_tsupport φ hn))
          simp only [hφz, norm_zero, zero_smul, zero_mul, mul_zero, le_refl]
      _ = _ := integral_const_mul _ _
  have hDzero : Tendsto (fun n => ∫ z, φ z • complexDbar (Fₙ n) z) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hnorm
      (by simpa only [mul_zero] using tendsto_const_nhds.mul hresLim)
  have hJzero : Tendsto (fun n => ∫ z, complexDbar φ z • Fₙ n z) atTop (𝓝 0) := by
    have heq : (fun n => ∫ z, complexDbar φ z • Fₙ n z) =
        (fun n => -(∫ z, φ z • complexDbar (Fₙ n) z)) := by
      funext n
      exact (hInt n).2.2
    rw [heq]
    simpa only [neg_zero] using hDzero.neg
  have hJlimit : Tendsto (fun n => ∫ z, complexDbar φ z • Fₙ n z) atTop
      (𝓝 (∫ z, complexDbar φ z • F z)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun n => norm_nonneg _) ?_ happrox
    intro n
    rw [← integral_sub (hInt n).1 hF]
    simpa only [smul_sub] using norm_integral_le_integral_norm
      (fun z => complexDbar φ z • (Fₙ n z - F z))
  exact tendsto_nhds_unique hJlimit hJzero

end DifferentialGeometry.Analysis
