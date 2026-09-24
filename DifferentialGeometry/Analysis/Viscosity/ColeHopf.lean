import DifferentialGeometry.Analysis.Calculus.SecondDerivative.Logarithm
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis.Viscosity
open scoped BigOperators
variable {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype κ]
theorem cole_hopf_upper_test
    (f : E → ℝ) (x d : E) (b : κ → E) (a : κ → κ → ℝ) (c : ℝ)
    (htests : ∀ psi : E → ℝ, ContDiffAt ℝ 2 psi x →
      IsLocalMin (fun y => f y - psi y) x →
        0 ≤ fderiv ℝ psi x d - ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ psi) x (b i) (b j) +
          (∑ i, ∑ j, a i j * fderiv ℝ psi x (b i) * fderiv ℝ psi x (b j)) + c)
    (phi : E → ℝ) (hphi : ContDiffAt ℝ 2 phi x)
    (hmax : IsLocalMax (fun y => Real.exp (-f y) - phi y) x) :
    fderiv ℝ phi x d - ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ phi) x (b i) (b j) -
      c * Real.exp (-f x) ≤ 0 := by
  let q : E → ℝ := fun y => phi y + (Real.exp (-f x) - phi x)
  have hq : ContDiffAt ℝ 2 q x := hphi.add contDiffAt_const
  have hqx : q x = Real.exp (-f x) := by dsimp [q]; ring
  have hpos : 0 < q x := hqx ▸ Real.exp_pos _
  let psi : E → ℝ := fun y => -Real.log (q y)
  have hpsi : ContDiffAt ℝ 2 psi x := (hq.log hpos.ne').neg
  have hmin : IsLocalMin (fun y => f y - psi y) x := by
    filter_upwards [hmax] with y hy
    have hle : Real.exp (-f y) ≤ q y := by dsimp only [q]; linarith
    have hh := Real.log_le_log (Real.exp_pos (-f y)) hle
    rw [Real.log_exp] at hh
    dsimp only [psi]
    rw [hqx, Real.log_exp]
    linarith
  have hDq : fderiv ℝ q = fderiv ℝ phi := by
    funext y
    exact fderiv_add_const _
  have hD (v : E) : fderiv ℝ psi x v = -(q x)⁻¹ * fderiv ℝ phi x v := by
    dsimp only [psi]
    rw [fderiv_fun_neg, fderiv.log (hq.differentiableAt (by norm_num)) hpos.ne', hDq]
    simp only [neg_apply, smul_apply, smul_eq_mul, neg_mul]
  have hDD (v w : E) : fderiv ℝ (fderiv ℝ psi) x v w =
      -(q x)⁻¹ * fderiv ℝ (fderiv ℝ phi) x v w +
        (q x)⁻¹ ^ 2 * fderiv ℝ phi x v * fderiv ℝ phi x w := by
    have heq : fderiv ℝ psi = -fderiv ℝ (fun y => Real.log (q y)) := by
      funext y
      exact fderiv_fun_neg
    rw [heq, fderiv_neg]
    simp only [neg_apply]
    rw [DifferentialGeometry.Analysis.fderiv_fderiv_log_apply hq hpos.ne' v w, hDq]
    ring
  have hsum :
      (∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ psi) x (b i) (b j)) -
          (∑ i, ∑ j, a i j * fderiv ℝ psi x (b i) * fderiv ℝ psi x (b j)) =
        -(q x)⁻¹ * ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ phi) x (b i) (b j) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hDD, hD, hD]
    ring
  have hh := htests psi hpsi hmin
  rw [hD] at hh
  have hnonneg : 0 ≤ -(q x)⁻¹ *
      (fderiv ℝ phi x d - ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ phi) x (b i) (b j)) + c := by
    linarith
  have hscaled := mul_nonneg hpos.le hnonneg
  rw [mul_add, ← mul_assoc, mul_neg, mul_inv_cancel₀ hpos.ne', neg_one_mul] at hscaled
  rw [hqx] at hscaled
  linarith

theorem cole_hopf_upper_test_add_time
    (f : ℝ × E → ℝ) (z : ℝ × E) (d : E) (b : κ → E) (a : κ → κ → ℝ) (c : ℝ)
    (q : ℝ → ℝ) (hq : ContDiffAt ℝ 2 q z.1)
    (htests : ∀ psi : ℝ × E → ℝ, ContDiffAt ℝ 2 psi z →
      IsLocalMin (fun y => f y - psi y) z →
        0 ≤ fderiv ℝ psi z (1, d) -
          (∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ psi) z (0, b i) (0, b j)) +
          (∑ i, ∑ j, a i j * fderiv ℝ psi z (0, b i) * fderiv ℝ psi z (0, b j)) + c + deriv q z.1)
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 2 phi z)
    (hmax : IsLocalMax (fun y => Real.exp (-(f y + q y.1)) - phi y) z) :
    fderiv ℝ phi z (1, d) - ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ phi) z (0, b i) (0, b j) -
      c * Real.exp (-(f z + q z.1)) ≤ 0 := by
  let Q : ℝ × E → ℝ := fun y => q y.1
  have hQ : ContDiffAt ℝ 2 Q z := hq.comp z contDiffAt_fst
  have hDQ (y : ℝ × E) (hy : ContDiffAt ℝ 2 q y.1) (v : ℝ × E) :
      fderiv ℝ Q y v = deriv q y.1 * v.1 := by
    have hh := (hy.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt y
      ((ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt)
    exact congrArg (fun L : (ℝ × E) →L[ℝ] ℝ => L v) hh.fderiv
  have hDDQ (v w : E) : fderiv ℝ (fderiv ℝ Q) z (0, v) (0, w) = 0 := by
    have heq : (fun y : ℝ × E => fderiv ℝ Q y (0, w)) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [continuous_fst.continuousAt.eventually (hq.eventually (by norm_num))] with y hy
      rw [hDQ y hy]
      exact mul_zero _
    have hd := (hQ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hh : fderiv ℝ (fun y => fderiv ℝ Q y (0, w)) z (0, v) =
        fderiv ℝ (fderiv ℝ Q) z (0, v) (0, w) := by
      rw [fderiv_clm_apply hd (differentiableAt_const (0, w))]
      simp
    rw [heq.fderiv_eq] at hh
    simpa using hh.symm
  apply cole_hopf_upper_test (fun y => f y + q y.1) z (1, d) (fun i => (0, b i)) a c _ phi hphi hmax
  intro psi hpsi hmin
  let chi : ℝ × E → ℝ := psi - Q
  have hchi : ContDiffAt ℝ 2 chi z := hpsi.sub hQ
  have hcontact : IsLocalMin (fun y => f y - chi y) z := by
    filter_upwards [hmin] with y hy
    dsimp only [chi, Pi.sub_apply, Q]
    linarith
  have hD (v : ℝ × E) : fderiv ℝ chi z v = fderiv ℝ psi z v - deriv q z.1 * v.1 := by
    rw [fderiv_sub (hpsi.differentiableAt (by norm_num)) (hQ.differentiableAt (by norm_num))]
    simp only [sub_apply, hDQ z hq]
  have hDD (v w : E) : fderiv ℝ (fderiv ℝ chi) z (0, v) (0, w) =
      fderiv ℝ (fderiv ℝ psi) z (0, v) (0, w) := by
    have hh := congrArg (fun A => A ![(0, v), (0, w)]) (iteratedFDeriv_sub_apply hpsi hQ)
    simp only [sub_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, hDDQ, sub_zero] at hh
    exact hh
  have hh := htests chi hchi hcontact
  simp only [hD, hDD, mul_one, mul_zero, sub_zero] at hh
  linarith
end DifferentialGeometry.Analysis.Viscosity
