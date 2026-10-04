import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Determinant monotonicity in the Loewner order (real positive semidefinite matrices)

* `Matrix.det_le_det_of_posSemidef_of_dotProduct_le`: if `A` and `B` are real positive
  semidefinite and `x ⬝ A x ≤ x ⬝ B x` for every `x`, then `det A ≤ det B`;
* `LinearMap.BilinForm.det_toMatrix_le_det_toMatrix`: the same statement for the Gram matrices
  `BilinForm.toMatrix b B₁`, `BilinForm.toMatrix b B₂` of two positive semidefinite symmetric
  bilinear forms with `B₁ v v ≤ B₂ v v`.

The positive-definite case follows the (private) argument of
`Analysis/Integration/Measure/Riemannian/MetricComparison.lean:52` (conjugation by `√B`, eigenvalues
of a contraction); the singular case uses a null vector of `B`, which is a null vector of `A`.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix MatrixOrder

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_le_one_of_posSemidef_of_dotProduct_le_self {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hray : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ x) :
    A.det ≤ 1 := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  refine Finset.prod_le_one₀ (fun i _ ↦ ?_) (fun i _ ↦ ?_)
  · exact_mod_cast hA.eigenvalues_nonneg i
  · have hle : hA.isHermitian.eigenvalues i ≤ 1 := by
      rw [hA.isHermitian.eigenvalues_eq i]
      set v := hA.isHermitian.eigenvectorBasis i
      have hv : ‖v‖ = 1 := hA.isHermitian.eigenvectorBasis.norm_eq_one i
      have hnorm : (⇑v : ι → ℝ) ⬝ᵥ ⇑v = 1 := by
        have h1 := EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ) v v
        rw [star_trivial] at h1
        have h2 : (⇑v : ι → ℝ) ⬝ᵥ ⇑v = ‖v‖ ^ 2 := by
          rw [← h1]
          exact real_inner_self_eq_norm_sq v
        rw [h2, hv, one_pow]
      simp only [star_trivial, RCLike.re_to_real]
      exact (hray ⇑v).trans hnorm.le
    exact_mod_cast hle

theorem det_le_det_of_posDef_of_dotProduct_le {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosDef) (hAB : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) :
    A.det ≤ B.det := by
  have quad_symm : ∀ (S : Matrix ι ι ℝ), Sᵀ = S → ∀ x z : ι → ℝ,
      x ⬝ᵥ (S *ᵥ z) = (S *ᵥ x) ⬝ᵥ z := by
    intro S hS x z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS]
  set P := CFC.sqrt B with hP_def
  have hP_nonneg : (0 : Matrix ι ι ℝ) ≤ P := by
    rw [hP_def]
    exact CFC.sqrt_nonneg B
  have hP_psd : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hP_nonneg
  have hP_herm : Pᴴ = P := hP_psd.isHermitian
  have hPsymm : Pᵀ = P := by
    ext i j
    simpa [Matrix.transpose_apply, star_trivial] using hP_psd.isHermitian.apply i j
  have hPP : P * P = B := by
    rw [hP_def]
    exact CFC.sqrt_mul_sqrt_self B (Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef)
  have hdetB_pos : 0 < B.det := hB.det_pos
  have hdetPP : P.det * P.det = B.det := by rw [← Matrix.det_mul, hPP]
  have hdetP_ne : P.det ≠ 0 := fun h0 ↦
    hdetB_pos.ne' (by rw [← hdetPP, h0, zero_mul])
  have hdetP_unit : IsUnit P.det := isUnit_iff_ne_zero.mpr hdetP_ne
  have hPinv_r : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdetP_unit
  have hPinv_l : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdetP_unit
  have hPinvsymm : (P⁻¹)ᵀ = P⁻¹ := by rw [Matrix.transpose_nonsing_inv, hPsymm]
  have hC_psd : (P⁻¹ * A * P⁻¹).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same P⁻¹
    rwa [Matrix.conjTranspose_nonsing_inv, hP_herm] at h
  have hC_ray : ∀ x : ι → ℝ, x ⬝ᵥ ((P⁻¹ * A * P⁻¹) *ᵥ x) ≤ x ⬝ᵥ x := by
    intro x
    have hPw : P *ᵥ (P⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hPinv_r, Matrix.one_mulVec]
    have e1 : x ⬝ᵥ ((P⁻¹ * A * P⁻¹) *ᵥ x) = (P⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (P⁻¹ *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact quad_symm P⁻¹ hPinvsymm x (A *ᵥ (P⁻¹ *ᵥ x))
    have e3 : (P⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (P⁻¹ *ᵥ x)) = x ⬝ᵥ x := by
      rw [← hPP, ← Matrix.mulVec_mulVec,
        quad_symm P hPsymm (P⁻¹ *ᵥ x) (P *ᵥ (P⁻¹ *ᵥ x)), hPw]
    calc x ⬝ᵥ ((P⁻¹ * A * P⁻¹) *ᵥ x) = (P⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (P⁻¹ *ᵥ x)) := e1
      _ ≤ (P⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (P⁻¹ *ᵥ x)) := hAB (P⁻¹ *ᵥ x)
      _ = x ⬝ᵥ x := e3
  have hdetC : (P⁻¹ * A * P⁻¹).det ≤ 1 :=
    det_le_one_of_posSemidef_of_dotProduct_le_self hC_psd hC_ray
  have hACM : P * (P⁻¹ * A * P⁻¹) * P = A := by
    rw [show P * (P⁻¹ * A * P⁻¹) * P = (P * P⁻¹) * A * (P⁻¹ * P) by simp only [mul_assoc]]
    rw [hPinv_r, hPinv_l, one_mul, mul_one]
  have hdetA : A.det = B.det * (P⁻¹ * A * P⁻¹).det := by
    have hcongr := congrArg Matrix.det hACM
    rw [Matrix.det_mul, Matrix.det_mul] at hcongr
    rw [← hcongr, ← hdetPP]
    ring
  rw [hdetA]
  exact mul_le_of_le_one_right hdetB_pos.le hdetC

/-- **Determinant monotonicity in the Loewner order.** For real positive semidefinite `A`, `B`
with `x ⬝ A x ≤ x ⬝ B x` for all `x`: `det A ≤ det B`. -/
theorem det_le_det_of_posSemidef_of_dotProduct_le {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hAB : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) :
    A.det ≤ B.det := by
  by_cases hBd : B.PosDef
  · exact det_le_det_of_posDef_of_dotProduct_le hA hBd hAB
  · have hex : ∃ x : ι → ℝ, x ≠ 0 ∧ x ⬝ᵥ (B *ᵥ x) ≤ 0 := by
      by_contra hne
      push Not at hne
      refine hBd (Matrix.PosDef.of_dotProduct_mulVec_pos hB.isHermitian fun x hx => ?_)
      simpa [star_trivial] using hne x hx
    obtain ⟨x, hx0, hxB⟩ := hex
    have hA0 : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by simpa [star_trivial] using hA.dotProduct_mulVec_nonneg x
    have hAx : A *ᵥ x = 0 := by
      have h : star x ⬝ᵥ A *ᵥ x = 0 := by
        rw [star_trivial]
        exact le_antisymm ((hAB x).trans hxB) hA0
      exact hA.dotProduct_mulVec_zero_iff.mp h
    have hdetA : A.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx0, hAx⟩
    rw [hdetA]
    exact hB.det_nonneg

end Matrix

namespace LinearMap.BilinForm

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι] [DecidableEq ι]

/-- The Gram matrix of a symmetric bilinear form with nonnegative diagonal values is positive
semidefinite. -/
theorem posSemidef_toMatrix (b : Module.Basis ι ℝ V) (B : LinearMap.BilinForm ℝ V)
    (hsymm : ∀ v w, B v w = B w v) (hpos : ∀ v, 0 ≤ B v v) :
    (toMatrix b B).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [toMatrix_apply, star_trivial]
    exact hsymm _ _
  · rw [star_trivial, dotProduct_toMatrix_mulVec]
    exact hpos _

/-- **Gram determinants are monotone** under the pointwise order of positive semidefinite
symmetric bilinear forms. -/
theorem det_toMatrix_le_det_toMatrix (b : Module.Basis ι ℝ V) {B₁ B₂ : LinearMap.BilinForm ℝ V}
    (hsymm₁ : ∀ v w, B₁ v w = B₁ w v) (hsymm₂ : ∀ v w, B₂ v w = B₂ w v)
    (hpos₁ : ∀ v, 0 ≤ B₁ v v) (hle : ∀ v, B₁ v v ≤ B₂ v v) :
    (toMatrix b B₁).det ≤ (toMatrix b B₂).det := by
  refine Matrix.det_le_det_of_posSemidef_of_dotProduct_le (posSemidef_toMatrix b B₁ hsymm₁ hpos₁)
    (posSemidef_toMatrix b B₂ hsymm₂ fun v => (hpos₁ v).trans (hle v)) fun x => ?_
  rw [dotProduct_toMatrix_mulVec, dotProduct_toMatrix_mulVec]
  exact hle _

end LinearMap.BilinForm
