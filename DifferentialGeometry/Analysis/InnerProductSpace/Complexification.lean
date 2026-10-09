import Mathlib.Analysis.InnerProductSpace.TensorProduct

set_option autoImplicit false

noncomputable section

open Complex
open scoped TensorProduct ComplexConjugate

namespace TensorProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private def complexInner (u v : ℂ ⊗[ℝ] H) : ℂ :=
  (inner ℝ u v : ℂ) - I * (inner ℝ u (I • v) : ℂ)

private theorem complexInner_add_left (u v w : ℂ ⊗[ℝ] H) :
    complexInner (u + v) w = complexInner u w + complexInner v w := by
  simp only [complexInner, inner_add_left, ofReal_add]
  ring

private theorem complexInner_add_right (u v w : ℂ ⊗[ℝ] H) :
    complexInner u (v + w) = complexInner u v + complexInner u w := by
  simp only [complexInner, smul_add, inner_add_right, ofReal_add]
  ring

private theorem complexInner_tmul (z w : ℂ) (x y : H) :
    complexInner (z ⊗ₜ[ℝ] x) (w ⊗ₜ[ℝ] y) = conj z * w * (inner ℝ x y : ℂ) := by
  apply Complex.ext <;>
    simp [complexInner, smul_tmul', smul_eq_mul, inner_tmul,
      Complex.inner, Complex.mul_re, Complex.mul_im] <;> ring_nf
  all_goals simp

private theorem complexInner_conj_symm (u v : ℂ ⊗[ℝ] H) :
    conj (complexInner v u) = complexInner u v := by
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    induction v using TensorProduct.inductionOn with
    | tmul w y =>
      simp only [complexInner_tmul, map_mul, conj_conj, conj_ofReal, real_inner_comm y x]
      ring
    | add a b ha hb =>
      simp only [complexInner_add_left, complexInner_add_right, map_add, ha, hb]
  | add a b ha hb =>
    simp only [complexInner_add_left, complexInner_add_right, map_add, ha, hb]

private theorem complexInner_smul_left (u v : ℂ ⊗[ℝ] H) (c : ℂ) :
    complexInner (c • u) v = conj c * complexInner u v := by
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    induction v using TensorProduct.inductionOn with
    | tmul w y =>
      simp only [smul_tmul', smul_eq_mul, complexInner_tmul, map_mul]
      ring
    | add a b ha hb =>
      simp only [complexInner_add_right, ha, hb, mul_add]
  | add a b ha hb =>
    simp only [smul_add, complexInner_add_left, ha, hb, mul_add]

private theorem complexInner_smul_right (u v : ℂ ⊗[ℝ] H) (c : ℂ) :
    complexInner u (c • v) = c * complexInner u v := by
  rw [← complexInner_conj_symm, complexInner_smul_left, map_mul, conj_conj,
    complexInner_conj_symm]

private theorem re_complexInner_self (u : ℂ ⊗[ℝ] H) :
    (complexInner u u).re = ‖u‖ ^ 2 := by
  simp only [complexInner, sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
    zero_mul, mul_zero, sub_zero, real_inner_self_eq_norm_sq]

instance complexInnerProductSpace : InnerProductSpace ℂ (ℂ ⊗[ℝ] H) where
  norm_smul_le c u := by
    have heq := re_complexInner_self (c • u)
    rw [complexInner_smul_left, complexInner_smul_right] at heq
    have heq' : ‖c • u‖ ^ 2 = (‖c‖ * ‖u‖) ^ 2 := by
      rw [← heq, ← mul_assoc, Complex.conj_mul', ← ofReal_pow]
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, re_complexInner_self]
      ring
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg c) (norm_nonneg u))).mp heq'.le
  inner := complexInner
  norm_sq_eq_re_inner u := (re_complexInner_self u).symm
  conj_inner_symm := complexInner_conj_symm
  add_left := complexInner_add_left
  smul_left := complexInner_smul_left

@[simp] theorem complex_inner_tmul (z w : ℂ) (x y : H) :
    inner ℂ (z ⊗ₜ[ℝ] x) (w ⊗ₜ[ℝ] y) = conj z * w * (inner ℝ x y : ℂ) :=
  complexInner_tmul z w x y

end TensorProduct

namespace ContinuousLinearMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

noncomputable def complexify (A : H →L[ℝ] K) : (ℂ ⊗[ℝ] H) →L[ℂ] (ℂ ⊗[ℝ] K) :=
  (A.toLinearMap.baseChange ℂ).mkContinuous ‖A‖ fun v => by
    change ‖A.toLinearMap.lTensor ℂ v‖ ≤ _
    rw [← lTensor_apply]
    exact (A.lTensor ℂ).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right (norm_lTensor_le ℂ A) (norm_nonneg v))

@[simp] theorem complexify_tmul (A : H →L[ℝ] K) (z : ℂ) (x : H) :
    A.complexify (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] A x := rfl

theorem norm_complexify (A : H →L[ℝ] K) : ‖A.complexify‖ = ‖A‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _
  · apply A.opNorm_le_bound (norm_nonneg _)
    intro x
    have h := A.complexify.le_opNorm (1 ⊗ₜ[ℝ] x)
    simpa only [complexify_tmul, TensorProduct.norm_tmul, norm_one, one_mul] using h

@[simp] theorem complexify_add (A B : H →L[ℝ] K) :
    (A + B).complexify = A.complexify + B.complexify := by
  ext v
  exact congrArg (fun f => f v) (LinearMap.baseChange_add (f := A.toLinearMap) (g := B.toLinearMap) (A := ℂ))

@[simp] theorem complexify_smul (r : ℝ) (A : H →L[ℝ] K) :
    (r • A).complexify = r • A.complexify := by
  ext v
  exact congrArg (fun f => f v) (LinearMap.baseChange_smul (f := A.toLinearMap) (A := ℂ) r)

noncomputable def complexifyₗᵢ :
    (H →L[ℝ] K) →ₗᵢ[ℝ] ((ℂ ⊗[ℝ] H) →L[ℂ] (ℂ ⊗[ℝ] K)) where
  toFun := complexify
  map_add' := complexify_add
  map_smul' := complexify_smul
  norm_map' := norm_complexify

end ContinuousLinearMap

namespace LinearMap.IsSymmetric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem complexify {A : H →L[ℝ] H} (hA : A.toLinearMap.IsSymmetric) :
    A.complexify.toLinearMap.IsSymmetric := by
  intro u v
  change inner ℂ (A.complexify u) v = inner ℂ u (A.complexify v)
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    induction v using TensorProduct.inductionOn with
    | tmul w y => simp only [ContinuousLinearMap.complexify_tmul,
        TensorProduct.complex_inner_tmul, hA.apply_clm x y]
    | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
  | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]

end LinearMap.IsSymmetric

namespace Submodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem complexify_starProjection_mem (P : Submodule ℝ H) [P.HasOrthogonalProjection]
    (u : ℂ ⊗[ℝ] H) : P.starProjection.complexify u ∈ P.baseChange ℂ := by
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    rw [ContinuousLinearMap.complexify_tmul]
    exact tmul_mem_baseChange_of_mem z (P.starProjection_apply_mem x)
  | add a b ha hb => simpa only [map_add] using (P.baseChange ℂ).add_mem ha hb

private theorem complexify_starProjection_eq_self (P : Submodule ℝ H) [P.HasOrthogonalProjection]
    {u : ℂ ⊗[ℝ] H} (hu : u ∈ P.baseChange ℂ) : P.starProjection.complexify u = u := by
  obtain ⟨v, rfl⟩ := hu
  induction v using TensorProduct.inductionOn with
  | tmul z x =>
    simp only [LinearMap.baseChange_tmul, coe_subtype, ContinuousLinearMap.complexify_tmul,
      starProjection_eq_self_iff.mpr x.property]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem sub_complexify_starProjection_mem_orthogonal (P : Submodule ℝ H)
    [P.HasOrthogonalProjection] (u : ℂ ⊗[ℝ] H) :
    u - P.starProjection.complexify u ∈ (P.baseChange ℂ)ᗮ := by
  apply (P.baseChange ℂ).mem_orthogonal' _ |>.mpr
  intro v hv
  rw [inner_sub_left]
  have h := P.starProjection_isSymmetric.complexify u v
  change inner ℂ (P.starProjection.complexify u) v =
    inner ℂ u (P.starProjection.complexify v) at h
  rw [complexify_starProjection_eq_self P hv] at h
  rw [h, sub_self]

instance HasOrthogonalProjection.baseChangeComplex (P : Submodule ℝ H)
    [P.HasOrthogonalProjection] : (P.baseChange ℂ).HasOrthogonalProjection where
  exists_orthogonal u := ⟨P.starProjection.complexify u, complexify_starProjection_mem P u,
    sub_complexify_starProjection_mem_orthogonal P u⟩

@[simp] theorem complexify_starProjection (P : Submodule ℝ H) [P.HasOrthogonalProjection] :
    P.starProjection.complexify = (P.baseChange ℂ).starProjection := by
  ext u
  exact ((P.baseChange ℂ).eq_starProjection_of_mem_orthogonal
    (complexify_starProjection_mem P u) (sub_complexify_starProjection_mem_orthogonal P u)).symm

end Submodule
