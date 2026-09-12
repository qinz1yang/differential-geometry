import DifferentialGeometry.Analysis.InnerProductSpace.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Filter InnerProductSpace
open scoped Topology ContDiff InnerProductSpace

private theorem second_partial_norm_sq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fun q => fderiv ℝ (fun y => ‖f y‖ ^ 2) q v) x w =
      2 * ⟪fderiv ℝ f x w, fderiv ℝ f x v⟫_ℝ +
        2 * ⟪f x, fderiv ℝ (fderiv ℝ f) x w v⟫_ℝ := by
  have hd := hf.differentiableAt (by norm_num)
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp : DifferentiableAt ℝ (fun q => fderiv ℝ f q v) x :=
    hdd.clm_apply (differentiableAt_const v)
  have hnear : (fun q => fderiv ℝ (fun y => ‖f y‖ ^ 2) q v) =ᶠ[𝓝 x]
      (fun q => 2 * ⟪f q, fderiv ℝ f q v⟫_ℝ) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    rw [(hq.differentiableAt (by norm_num)).hasFDerivAt.norm_sq.fderiv]
    simp [two_smul, two_mul]
  rw [hnear.fderiv_eq]
  erw [fderiv_const_mul (hd.inner ℝ hp) (2 : ℝ)]
  simp only [_root_.smul_apply, smul_eq_mul]
  have hpderiv : fderiv ℝ (fun q => fderiv ℝ f q v) x w =
      fderiv ℝ (fderiv ℝ f) x w v := by
    rw [fderiv_clm_apply hdd (differentiableAt_const v)]
    simp
  rw [fderiv_inner_apply ℝ hd hp, hpderiv]
  ring

theorem ContDiffAt.laplacian_norm_sq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian (fun y => ‖f y‖ ^ 2) x =
      2 * ⟪f x, Laplacian.laplacian f x⟫_ℝ +
        2 * (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x) := by
  simp only [ContinuousLinearMap.hilbertSchmidtInner, real_inner_self_eq_norm_sq]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdd := ((hf.norm_sq ℝ).fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)
  have he (v : E) :
      fderiv ℝ (fderiv ℝ (fun y => ‖f y‖ ^ 2)) x v v =
        fderiv ℝ (fun q => fderiv ℝ (fun y => ‖f y‖ ^ 2) q v) x v := by
    rw [fderiv_clm_apply hdd (differentiableAt_const v)]
    simp
  simp only [he, second_partial_norm_sq hf, real_inner_self_eq_norm_sq,
    Finset.sum_add_distrib, ← Finset.mul_sum, inner_sum]
  ring


theorem ContDiffAt.le_laplacian_norm_sq_of_norm_laplacian_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) {β : ℝ}
    (hΔ : ‖Laplacian.laplacian f x‖ ≤
      β * (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x)) :
    2 * (1 - β * ‖f x‖) * (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x) ≤
      Laplacian.laplacian (fun y => ‖f y‖ ^ 2) x := by
  have hi := (abs_le.mp (abs_real_inner_le_norm (f x) (Laplacian.laplacian f x))).1
  have hm := mul_le_mul_of_nonneg_left hΔ (norm_nonneg (f x))
  rw [hf.laplacian_norm_sq]
  nlinarith only [hi, hm]


theorem ContDiffAt.laplacian_norm_sq_nonneg_of_norm_laplacian_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) {β : ℝ}
    (hΔ : ‖Laplacian.laplacian f x‖ ≤
      β * (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x))
    (hsmall : β * ‖f x‖ ≤ 1) :
    0 ≤ Laplacian.laplacian (fun y => ‖f y‖ ^ 2) x := by
  have henergy : 0 ≤ (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x) := by
    unfold ContinuousLinearMap.hilbertSchmidtInner
    exact Finset.sum_nonneg fun _ _ => real_inner_self_nonneg
  exact (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hsmall)) henergy).trans
    (hf.le_laplacian_norm_sq_of_norm_laplacian_le hΔ)
