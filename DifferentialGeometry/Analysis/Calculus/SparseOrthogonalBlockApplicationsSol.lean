import DifferentialGeometry.Analysis.Calculus.OrthogonalBlockDerivatives
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.X81Sol

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]

theorem orthogonalBlocks_active_derivative_bounds {f : ∀ i, E → F i}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x : E) (s : Finset ι) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ i ∈ s, ‖fderiv ℝ (f i) x‖ ≤ A)
    (hsecond : ∀ i ∈ s, ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ B)
    (hfirstzero : ∀ i ∉ s, fderiv ℝ (f i) x = 0)
    (hsecondzero : ∀ i ∉ s, fderiv ℝ (fderiv ℝ (f i)) x = 0) :
    ‖fderiv ℝ (orthogonalBlocks f) x‖ ≤ Real.sqrt (s.card : ℝ) * A ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x‖ ≤ Real.sqrt (s.card : ℝ) * B := by
  let W := orthogonalBlocks f
  have hW := contDiff_orthogonalBlocks hf
  have hWd := hW.differentiable (by norm_num)
  have hWdd : Differentiable ℝ (fderiv ℝ W) :=
    (hW.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  let P (i : ι) : PiLp 2 F →L[ℝ] F i :=
    (ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℝ F).toContinuousLinearMap
  have hD (i : ι) : fderiv ℝ (f i) =
      (ContinuousLinearMap.compL ℝ E (PiLp 2 F) (F i) (P i)) ∘ fderiv ℝ W := by
    funext y
    exact ((P i).hasFDerivAt.comp y (hWd y).hasFDerivAt).fderiv
  have hfirsteq (i : ι) (v : E) : (fderiv ℝ W x v) i = fderiv ℝ (f i) x v := by
    rw [hD]
    rfl
  have hsecondeq (i : ι) (v w : E) :
      (fderiv ℝ (fderiv ℝ W) x v w) i = fderiv ℝ (fderiv ℝ (f i)) x v w := by
    rw [hD, fderiv_comp x (ContinuousLinearMap.compL ℝ E (PiLp 2 F) (F i) (P i)).differentiableAt
      (hWdd x), ContinuousLinearMap.fderiv]
    rfl
  constructor
  · apply (fderiv ℝ W x).norm_le_sqrt_active_blocks s hA
    · intro v i hi
      rw [hfirsteq]
      exact ((fderiv ℝ (f i) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hfirst i hi) (norm_nonneg v))
    · intro v i hi
      rw [hfirsteq, hfirstzero i hi]
      rfl
  · apply (fderiv ℝ (fderiv ℝ W) x).opNorm_le_bound (by positivity)
    intro v
    have h := (fderiv ℝ (fderiv ℝ W) x v).norm_le_sqrt_active_blocks s
      (B := B * ‖v‖) (by positivity)
      (fun w i hi => by
        rw [hsecondeq]
        exact ((fderiv ℝ (fderiv ℝ (f i)) x).le_opNorm₂ v w).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hsecond i hi) (norm_nonneg v)) (norm_nonneg w)))
      (fun w i hi => by rw [hsecondeq, hsecondzero i hi]; rfl)
    simpa only [mul_assoc] using h

theorem orthogonalBlocks_active_derivative_modulus {f : ∀ i, E → F i}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (D : Set E) (hD : Convex ℝ D)
    (active : E → Finset ι) {N : ℕ} (hcard : ∀ x ∈ D, (active x).card ≤ N)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ x ∈ D, ∀ i ∈ active x, ‖fderiv ℝ (f i) x‖ ≤ A)
    (hsecond : ∀ x ∈ D, ∀ i ∈ active x, ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ B)
    (hfirstzero : ∀ x ∈ D, ∀ i ∉ active x, fderiv ℝ (f i) x = 0)
    (hsecondzero : ∀ x ∈ D, ∀ i ∉ active x, fderiv ℝ (fderiv ℝ (f i)) x = 0) :
    (∀ x ∈ D, ‖fderiv ℝ (orthogonalBlocks f) x‖ ≤ Real.sqrt (N : ℝ) * A ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x‖ ≤ Real.sqrt (N : ℝ) * B) ∧
      ∀ x ∈ D, ∀ y ∈ D,
        ‖fderiv ℝ (orthogonalBlocks f) y - fderiv ℝ (orthogonalBlocks f) x‖ ≤
          Real.sqrt (N : ℝ) * B * ‖y - x‖ := by
  have hb (x : E) (hx : x ∈ D) :
      ‖fderiv ℝ (orthogonalBlocks f) x‖ ≤ Real.sqrt (N : ℝ) * A ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x‖ ≤ Real.sqrt (N : ℝ) * B := by
    have h := orthogonalBlocks_active_derivative_bounds hf x (active x) hA hB
      (hfirst x hx) (hsecond x hx) (hfirstzero x hx) (hsecondzero x hx)
    have hr := Real.sqrt_le_sqrt (show ((active x).card : ℝ) ≤ N by exact_mod_cast hcard x hx)
    exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hr hA),
      h.2.trans (mul_le_mul_of_nonneg_right hr hB)⟩
  refine ⟨hb, ?_⟩
  intro x hx y hy
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ((contDiff_orthogonalBlocks hf).fderiv_right
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num) z)
    (fun z hz => (hb z hz).2) hD hx hy

theorem orthogonalBlocks_tsupport_active_derivative_modulus {f : ∀ i, E → F i}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (D : Set E) (hD : Convex ℝ D)
    (active : E → Finset ι) {N : ℕ} (hcard : ∀ x ∈ D, (active x).card ≤ N)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ x ∈ D, ∀ i ∈ active x, ‖fderiv ℝ (f i) x‖ ≤ A)
    (hsecond : ∀ x ∈ D, ∀ i ∈ active x, ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ B)
    (hinactive : ∀ x ∈ D, ∀ i ∉ active x, x ∉ tsupport (f i)) :
    (∀ x ∈ D, ‖fderiv ℝ (orthogonalBlocks f) x‖ ≤ Real.sqrt (N : ℝ) * A ∧
      ‖fderiv ℝ (fderiv ℝ (orthogonalBlocks f)) x‖ ≤ Real.sqrt (N : ℝ) * B) ∧
      ∀ x ∈ D, ∀ y ∈ D,
        ‖fderiv ℝ (orthogonalBlocks f) y - fderiv ℝ (orthogonalBlocks f) x‖ ≤
          Real.sqrt (N : ℝ) * B * ‖y - x‖ := by
  apply orthogonalBlocks_active_derivative_modulus hf D hD active hcard hA hB hfirst hsecond
  · intro x hx i hi
    exact fderiv_of_notMem_tsupport ℝ (hinactive x hx i hi)
  · intro x hx i hi
    exact fderiv_of_notMem_tsupport ℝ (fun h => hinactive x hx i hi (tsupport_fderiv_subset ℝ h))

end DifferentialGeometry.Analysis.X81Sol
