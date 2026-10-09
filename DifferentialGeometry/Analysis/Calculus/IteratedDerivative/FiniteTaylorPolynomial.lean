import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.DirectionalJets
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Analysis.Analytic.IteratedFDeriv

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The polynomial with the finite derivatives of `f` at `x` as coefficients. -/
def finiteTaylorPolynomial (f : E → F) (x : E) (N : ℕ) (z : E) : F :=
  ∑ k ∈ Finset.range (N + 1),
    (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => z - x)

private def finiteTaylorCoefficients (f : E → F) (x : E) (N : ℕ) :
    FormalMultilinearSeries ℝ E F :=
  fun k => if k ≤ N then (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x else 0

private theorem finiteTaylorPolynomial_hasFiniteFPowerSeries
    (f : E → F) (x : E) (N : ℕ) :
    HasFiniteFPowerSeriesOnBall (finiteTaylorPolynomial f x N)
      (finiteTaylorCoefficients f x N) x (N + 1) ∞ := by
  refine HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
  · intro k hk
    simp only [finiteTaylorCoefficients, ite_eq_right (by omega : ¬ k ≤ N)]
  · intro y _
    unfold finiteTaylorPolynomial
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp only [finiteTaylorCoefficients, ite_eq_left hkN,
      _root_.smul_apply, add_sub_cancel_left]

private theorem cpolynomialOn_finiteTaylorPolynomial
    (f : E → F) (x : E) (N : ℕ) :
    CPolynomialOn ℝ (finiteTaylorPolynomial f x N) univ := by
  intro y _
  exact (finiteTaylorPolynomial_hasFiniteFPowerSeries f x N).cpolynomialAt_of_mem (by simp)

/-- Finite Taylor polynomials are smooth even when no regularity of `f` is assumed. -/
theorem contDiff_finiteTaylorPolynomial (f : E → F) (x : E) (N : ℕ) :
    ContDiff ℝ ∞ (finiteTaylorPolynomial f x N) :=
  contDiffOn_univ.mp (cpolynomialOn_finiteTaylorPolynomial f x N).contDiffOn

theorem finiteTaylorPolynomial_apply (f : E → F) (x : E) (N : ℕ) :
    finiteTaylorPolynomial f x N x = f x := by
  have h := (finiteTaylorPolynomial_hasFiniteFPowerSeries f x N).toHasFPowerSeriesOnBall.coeff_zero
    (fun _ => 0)
  simpa only [finiteTaylorCoefficients, ite_eq_left (Nat.zero_le N), Nat.factorial_zero,
    Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply] using h.symm

/-- Only finite differentiability of the original map is used in finite jet matching. -/
theorem iteratedFDeriv_finiteTaylorPolynomial
    {f : E → F} {x : E} {N k : ℕ}
    (hf : ContDiffAt ℝ N f x) (hk : k ≤ N) :
    iteratedFDeriv ℝ k (finiteTaylorPolynomial f x N) x =
      iteratedFDeriv ℝ k f x := by
  ext v
  rw [(finiteTaylorPolynomial_hasFiniteFPowerSeries f x N).toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum
    (cpolynomialOn_finiteTaylorPolynomial f x N).analyticOn]
  have hterm (σ : Equiv.Perm (Fin k)) :
      finiteTaylorCoefficients f x N k (fun i => v (σ i)) =
        (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x v := by
    simp only [finiteTaylorCoefficients, ite_eq_left hk, _root_.smul_apply]
    congr 1
    have hperm := (hf.of_le (by exact_mod_cast hk)).iteratedFDeriv_perm σ
    exact congrArg (fun A : E [×k]→L[ℝ] F => A v) hperm
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]

theorem fderiv_finiteTaylorPolynomial
    {f : E → F} {x : E} {N : ℕ}
    (hf : ContDiffAt ℝ N f x) (hN : 1 ≤ N) :
    fderiv ℝ (finiteTaylorPolynomial f x N) x = fderiv ℝ f x := by
  ext v
  have h := congrArg (fun A : E [×1]→L[ℝ] F => A (fun _ => v))
    (iteratedFDeriv_finiteTaylorPolynomial hf hN)
  simpa only [iteratedFDeriv_one_apply] using h

/-- A smooth local coordinate replacement with the same finite jet, in chosen neighborhoods. -/
theorem exists_smooth_localEquiv_finiteTaylorPolynomial [CompleteSpace E]
    {f : E → F} {x : E} {N : ℕ}
    (hf : ContDiffAt ℝ N f x) (hN : 1 ≤ N)
    (hDf : (fderiv ℝ f x).IsInvertible)
    {U : Set E} {V : Set F} (hU : IsOpen U) (hx : x ∈ U)
    (hV : IsOpen V) (hfx : f x ∈ V) :
    ∃ e : OpenPartialHomeomorph E F,
      x ∈ e.source ∧ e.source ⊆ U ∧ e.target ⊆ V ∧
      (e : E → F) = finiteTaylorPolynomial f x N ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      e x = f x ∧ fderiv ℝ e x = fderiv ℝ f x ∧
      ∀ k ≤ N, iteratedFDeriv ℝ k e x = iteratedFDeriv ℝ k f x := by
  let P := finiteTaylorPolynomial f x N
  have hP : ContDiff ℝ ∞ P := contDiff_finiteTaylorPolynomial f x N
  obtain ⟨A, hA⟩ := hDf
  have hDP : HasFDerivAt P (A : E →L[ℝ] F) x := by
    rw [hA, ← fderiv_finiteTaylorPolynomial hf hN]
    exact (hP.differentiable (by simp) x).hasFDerivAt
  let D := U ∩ P ⁻¹' V
  have hD : IsOpen D := hU.inter (hV.preimage hP.continuous)
  have hxD : x ∈ D := by
    refine ⟨hx, ?_⟩
    change finiteTaylorPolynomial f x N x ∈ V
    rwa [finiteTaylorPolynomial_apply]
  obtain ⟨e, hxe, heD, hesmooth, heinvsmooth, heP⟩ :=
    exists_localInverse_of_hasFDerivAt_equiv hP.contDiffOn hD hxD hDP
  have heq : (e : E → F) = P := funext heP
  have hetarget : e.target ⊆ V := by
    intro y hy
    have h := (heD (e.map_target hy)).2
    change P (e.symm y) ∈ V at h
    rw [← heP (e.symm y), e.right_inv hy] at h
    exact h
  refine ⟨e, hxe, fun y hy => (heD hy).1, hetarget, heq,
    hesmooth, heinvsmooth, ?_, ?_, ?_⟩
  · rw [heP x]
    exact finiteTaylorPolynomial_apply f x N
  · rw [heq]
    exact fderiv_finiteTaylorPolynomial hf hN
  · intro k hk
    rw [heq]
    exact iteratedFDeriv_finiteTaylorPolynomial hf hk

end DifferentialGeometry.Analysis
