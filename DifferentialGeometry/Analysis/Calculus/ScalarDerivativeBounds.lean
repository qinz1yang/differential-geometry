import DifferentialGeometry.Analysis.Calculus.SecondDerivativeComposition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.GCongr

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem unit_scalar_product_derivative_bounds {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) {x : E} {a b A B : ℝ}
    (hfv : |f x| ≤ 1) (hgv : |g x| ≤ 1)
    (hDf : ‖fderiv ℝ f x‖ ≤ a) (hDg : ‖fderiv ℝ g x‖ ≤ b)
    (hDDf : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ A)
    (hDDg : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ B) :
    ‖fderiv ℝ (fun y => f y * g y) x‖ ≤ a + b ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x‖ ≤ A + 2 * a * b + B := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hDf
  have hA : 0 ≤ A := (norm_nonneg _).trans hDDf
  let T : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hT : ‖T‖ = 1 := ContinuousLinearMap.opNorm_lsmul ℝ ℝ
  have hf' := hf.differentiable (by norm_num)
  have hg' := hg.differentiable (by norm_num)
  have hDf' : Differentiable ℝ (fderiv ℝ f) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hf).2.2.differentiable (by norm_num)
  have hDg' : Differentiable ℝ (fderiv ℝ g) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hg).2.2.differentiable (by norm_num)
  have h1 := T.norm_fderiv_bilinear_le (hf' x) (hg' x)
  have h2 := T.norm_second_fderiv_bilinear_le hf' hg' (hDf' x) (hDg' x)
  simp only [hT, one_mul, Real.norm_eq_abs] at h1 h2
  constructor
  · apply h1.trans
    calc
      _ ≤ 1 * b + a * 1 := by gcongr
      _ = _ := by ring
  · apply h2.trans
    calc
      _ ≤ 1 * B + 2 * a * b + A * 1 := by gcongr
      _ = _ := by ring

theorem finite_sum_derivative_bounds {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {f : ι → E → H}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) {a b : ℝ}
    (hfirst : ∀ i x, ‖fderiv ℝ (f i) x‖ ≤ a)
    (hsecond : ∀ i x, ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ b) (x : E) :
    ‖fderiv ℝ (fun y => ∑ i, f i y) x‖ ≤ (Fintype.card ι : ℝ) * a ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => ∑ i, f i y)) x‖ ≤ (Fintype.card ι : ℝ) * b := by
  have hd (i : ι) := (hf i).differentiable (by norm_num)
  have hDd (i : ι) : Differentiable ℝ (fderiv ℝ (f i)) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp (hf i)).2.2.differentiable (by norm_num)
  have heq : fderiv ℝ (fun y => ∑ i, f i y) = fun y => ∑ i, fderiv ℝ (f i) y := by
    funext y
    exact fderiv_fun_sum (fun i _ => hd i y)
  rw [heq, fderiv_fun_sum (fun i _ => hDd i x)]
  constructor
  · exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => hfirst i x))
  · exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => hsecond i x))

end DifferentialGeometry.Analysis
