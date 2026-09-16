import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace EuclideanSpace

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable def equivProdLast (n : ℕ) :
    EuclideanSpace 𝕜 (Fin (n + 1)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × 𝕜 :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun x => (WithLp.toLp 2 (fun i => x i.castSucc), x (Fin.last n))
    invFun := fun p => WithLp.toLp 2 (Fin.snoc (fun i => p.1 i) p.2)
    left_inv := by
      intro x
      ext i
      cases i using Fin.lastCases <;> simp
    right_inv := by
      intro p
      apply Prod.ext
      · ext i
        simp
      · simp
    map_add' := by
      intro x y
      apply Prod.ext
      · ext i
        rfl
      · rfl
    map_smul' := by
      intro a x
      apply Prod.ext
      · ext i
        rfl
      · rfl }

@[simp] theorem equivProdLast_fst_apply (n : ℕ) (x : EuclideanSpace 𝕜 (Fin (n + 1)))
    (i : Fin n) : (equivProdLast n x).1 i = x i.castSucc := rfl

@[simp] theorem equivProdLast_snd (n : ℕ) (x : EuclideanSpace 𝕜 (Fin (n + 1))) :
    (equivProdLast n x).2 = x (Fin.last n) := rfl

@[simp] theorem equivProdLast_symm_castSucc (n : ℕ) (p : EuclideanSpace 𝕜 (Fin n) × 𝕜)
    (i : Fin n) : (equivProdLast n).symm p i.castSucc = p.1 i := by
  simp [equivProdLast]

@[simp] theorem equivProdLast_symm_last (n : ℕ) (p : EuclideanSpace 𝕜 (Fin n) × 𝕜) :
    (equivProdLast n).symm p (Fin.last n) = p.2 := by
  simp [equivProdLast]

theorem norm_sq_equivProdLast (n : ℕ) (x : EuclideanSpace 𝕜 (Fin (n + 1))) :
    ‖x‖ ^ 2 = ‖(equivProdLast n x).1‖ ^ 2 + ‖(equivProdLast n x).2‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc, equivProdLast_fst_apply,
    equivProdLast_snd]

theorem norm_sq_equivProdLast_symm (n : ℕ) (p : EuclideanSpace 𝕜 (Fin n) × 𝕜) :
    ‖(equivProdLast n).symm p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    norm_sq_equivProdLast n ((equivProdLast n).symm p)

theorem isometry_equivProdLast_symm_const {𝕜 : Type*} [RCLike 𝕜] (n : ℕ) (a : 𝕜) :
    Isometry (fun x : EuclideanSpace 𝕜 (Fin n) => (equivProdLast n).symm (x, a)) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, ← map_sub]
  change ‖(equivProdLast n).symm (x - y, a - a)‖ = dist x y
  rw [sub_self, dist_eq_norm]
  have h := norm_sq_equivProdLast_symm n (x - y, (0 : 𝕜))
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  nlinarith [norm_nonneg ((equivProdLast n).symm (x - y, (0 : 𝕜))), norm_nonneg (x - y)]

end EuclideanSpace
