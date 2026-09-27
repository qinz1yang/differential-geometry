import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

private def blockTopRow (D : Matrix m m ℝ) (B : Matrix m n ℝ) :
    (m ⊕ n → ℝ) →ₗ[ℝ] (m → ℝ) :=
  D.mulVecLin.comp (LinearMap.funLeft ℝ ℝ Sum.inl) +
    B.mulVecLin.comp (LinearMap.funLeft ℝ ℝ Sum.inr)

private theorem block_kernel_eq_top_kernel
    (D : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n m ℝ) (A : Matrix n n ℝ)
    (hD : IsUnit D.det) (hr : (Matrix.fromBlocks D B C A).rank = Fintype.card m) :
    LinearMap.ker (Matrix.fromBlocks D B C A).mulVecLin =
      LinearMap.ker (blockTopRow D B) := by
  have hle : LinearMap.ker (Matrix.fromBlocks D B C A).mulVecLin ≤
      LinearMap.ker (blockTopRow D B) := by
    intro v hv
    change (Matrix.fromBlocks D B C A) *ᵥ v = 0 at hv
    rw [Matrix.fromBlocks_mulVec] at hv
    change D *ᵥ (v ∘ Sum.inl) + B *ᵥ (v ∘ Sum.inr) = 0
    exact congrArg (fun w : m ⊕ n → ℝ => w ∘ Sum.inl) hv
  have hsurj : Function.Surjective (blockTopRow D B) := by
    intro v
    refine ⟨Sum.elim (D⁻¹ *ᵥ v) 0, ?_⟩
    change D *ᵥ (D⁻¹ *ᵥ v) + B *ᵥ 0 = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv D hD,
      Matrix.one_mulVec, Matrix.mulVec_zero, add_zero]
  have htop := (blockTopRow D B).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_pi] at htop
  have hfull := (Matrix.fromBlocks D B C A).mulVecLin.finrank_range_add_finrank_ker
  change (Matrix.fromBlocks D B C A).rank +
    Module.finrank ℝ (LinearMap.ker (Matrix.fromBlocks D B C A).mulVecLin) =
      Module.finrank ℝ (m ⊕ n → ℝ) at hfull
  rw [hr] at hfull
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

def blockKernelGraph (D : Matrix m m ℝ) (B : Matrix m n ℝ) :
    (n → ℝ) →ₗ[ℝ] (m ⊕ n → ℝ) where
  toFun u := Sum.elim (-(D⁻¹ *ᵥ (B *ᵥ u))) u
  map_add' u v := by
    funext i
    cases i <;> simp [Matrix.mulVec_add, add_comm]
  map_smul' c u := by
    funext i
    cases i <;> simp [Matrix.mulVec_smul]

theorem blockKernelGraph_mem_ker
    (D : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n m ℝ) (A : Matrix n n ℝ)
    (hD : IsUnit D.det) (hr : (Matrix.fromBlocks D B C A).rank = Fintype.card m)
    (u : n → ℝ) :
    blockKernelGraph D B u ∈ LinearMap.ker (Matrix.fromBlocks D B C A).mulVecLin := by
  rw [block_kernel_eq_top_kernel D B C A hD hr]
  change D *ᵥ (-(D⁻¹ *ᵥ (B *ᵥ u))) + B *ᵥ u = 0
  rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv D hD,
    Matrix.one_mulVec, neg_add_cancel]

private theorem blockKernelGraph_reconstruct
    (D : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n m ℝ) (A : Matrix n n ℝ)
    (hD : IsUnit D.det) (hr : (Matrix.fromBlocks D B C A).rank = Fintype.card m)
    (v : LinearMap.ker (Matrix.fromBlocks D B C A).mulVecLin) :
    blockKernelGraph D B (v.1 ∘ Sum.inr) = v.1 := by
  have hv : v.1 ∈ LinearMap.ker (blockTopRow D B) :=
    (block_kernel_eq_top_kernel D B C A hD hr).le v.property
  change D *ᵥ (v.1 ∘ Sum.inl) + B *ᵥ (v.1 ∘ Sum.inr) = 0 at hv
  have hleft := congrArg (fun w : m → ℝ => D⁻¹ *ᵥ w)
    (eq_neg_of_add_eq_zero_left hv)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D hD,
    Matrix.one_mulVec, Matrix.mulVec_neg] at hleft
  funext i
  cases i with
  | inl j => exact congrFun hleft.symm j
  | inr j => rfl

def blockKernelGraphEquiv
    (D : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n m ℝ) (A : Matrix n n ℝ)
    (hD : IsUnit D.det) (hr : (Matrix.fromBlocks D B C A).rank = Fintype.card m) :
    (n → ℝ) ≃ₗ[ℝ] LinearMap.ker (Matrix.fromBlocks D B C A).mulVecLin where
  toFun u := ⟨blockKernelGraph D B u, blockKernelGraph_mem_ker D B C A hD hr u⟩
  invFun v := v.1 ∘ Sum.inr
  left_inv _ := rfl
  right_inv v := Subtype.ext (blockKernelGraph_reconstruct D B C A hD hr v)
  map_add' u v := Subtype.ext ((blockKernelGraph D B).map_add u v)
  map_smul' c u := Subtype.ext ((blockKernelGraph D B).map_smul c u)

theorem blockKernelGraphEquiv_apply
    (D : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n m ℝ) (A : Matrix n n ℝ)
    (hD : IsUnit D.det) (hr : (Matrix.fromBlocks D B C A).rank = Fintype.card m)
    (u : n → ℝ) :
    ((blockKernelGraphEquiv D B C A hD hr u) : m ⊕ n → ℝ) =
      Sum.elim (-(D⁻¹ *ᵥ (B *ᵥ u))) u := rfl

theorem blockKernelGraphEquiv_symm_apply
    (D : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n m ℝ) (A : Matrix n n ℝ)
    (hD : IsUnit D.det) (hr : (Matrix.fromBlocks D B C A).rank = Fintype.card m)
    (v : LinearMap.ker (Matrix.fromBlocks D B C A).mulVecLin) :
    (blockKernelGraphEquiv D B C A hD hr).symm v = v.1 ∘ Sum.inr := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
