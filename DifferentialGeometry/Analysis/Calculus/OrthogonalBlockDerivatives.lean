import DifferentialGeometry.Analysis.InnerProductSpace.BlockNormBounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem second_fderiv_postcomp_apply {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : E → F} (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fderiv ℝ (L ∘ f)) x v w = L (fderiv ℝ (fderiv ℝ f) x v w) := by
  let T := ContinuousLinearMap.compL ℝ E F G L
  have hfd := hf.differentiable (by norm_num)
  have hDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have heq : fderiv ℝ (L ∘ f) = T ∘ fderiv ℝ f := by
    funext y
    exact (L.hasFDerivAt.comp y (hfd y).hasFDerivAt).fderiv
  rw [heq, fderiv_comp x T.differentiableAt (hDf x), T.fderiv]
  rfl

variable {ι : Type*} [Fintype ι] {F : ι → Type*}
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]

noncomputable def orthogonalBlocks (f : ∀ i, E → F i) (x : E) : PiLp 2 F :=
  WithLp.toLp 2 (fun i => f i x)

theorem contDiff_orthogonalBlocks {f : ∀ i, E → F i} {n : WithTop ℕ∞}
    (hf : ∀ i, ContDiff ℝ n (f i)) : ContDiff ℝ n (orthogonalBlocks f) :=
  (PiLp.continuousLinearEquiv 2 ℝ F).symm.contDiff.comp (contDiff_pi.mpr hf)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [∀ i, InnerProductSpace ℝ (F i)] in
theorem norm_orthogonalBlocks_le {f : ∀ i, E → F i} {x : E} {A : ℝ}
    (hA : 0 ≤ A) (hv : ∀ i, ‖f i x‖ ≤ A) :
    ‖orthogonalBlocks f x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * A := by
  have hsq : ‖orthogonalBlocks f x‖ ^ 2 ≤ (Fintype.card ι : ℝ) * A ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact (Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ =>
      sq_le_sq₀ (norm_nonneg (f i x)) hA |>.mpr (hv i))).trans_eq (by simp)
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card ι by positivity)
  have hnonneg := mul_nonneg (Real.sqrt_nonneg (Fintype.card ι : ℝ)) hA
  nlinarith [norm_nonneg (orthogonalBlocks f x)]

theorem orthogonalBlocks_derivative_bounds {f : ∀ i, E → F i}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hvalue : ∀ i x, ‖f i x‖ ≤ A) (hfirst : ∀ i x, ‖fderiv ℝ (f i) x‖ ≤ B)
    (hsecond : ∀ i x, ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ C) (x : E) :
    ‖orthogonalBlocks f x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * A ∧
      ‖fderiv ℝ (orthogonalBlocks f) x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * B ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * C := by
  have hW := contDiff_orthogonalBlocks hf
  have hWd := hW.differentiable (by norm_num)
  let P (i : ι) : PiLp 2 F →L[ℝ] F i :=
    (ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℝ F).toContinuousLinearMap
  have hD (i : ι) : fderiv ℝ (f i) x = (P i).comp (fderiv ℝ (orthogonalBlocks f) x) :=
    ((P i).hasFDerivAt.comp x (hWd x).hasFDerivAt).fderiv
  have hDD (i : ι) (v w : E) :
      fderiv ℝ (fderiv ℝ (f i)) x v w = (fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x v w) i :=
    second_fderiv_postcomp_apply (P i) hW x v w
  refine ⟨norm_orthogonalBlocks_le hA (fun i => hvalue i x), ?_, ?_⟩
  · have hh := (fderiv ℝ (orthogonalBlocks f) x).norm_le_sqrt_active_blocks Finset.univ hB
      (fun v i _ => ?_) (fun _ i hi => False.elim (hi (Finset.mem_univ i)))
    · simpa only [Finset.card_univ] using hh
    · have hi : (fderiv ℝ (orthogonalBlocks f) x v) i = fderiv ℝ (f i) x v := by
        rw [hD]
        rfl
      rw [hi]
      exact ((fderiv ℝ (f i) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hfirst i x) (norm_nonneg v))
  · apply (fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x).opNorm_le_bound (by positivity)
    intro v
    have hh := (fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x v).norm_le_sqrt_active_blocks
      Finset.univ (B := C * ‖v‖) (by positivity)
      (fun w i _ => ?_) (fun _ i hi => False.elim (hi (Finset.mem_univ i)))
    · simpa only [Finset.card_univ, mul_assoc] using hh
    · rw [← hDD]
      exact ((fderiv ℝ (fderiv ℝ (f i)) x).le_opNorm₂ v w).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hsecond i x) (norm_nonneg v)) (norm_nonneg w))

end DifferentialGeometry.Analysis
