import DifferentialGeometry.Geometry.Lorentz.InnerProduct
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

noncomputable section

namespace DifferentialGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem lorentzIsometry_norm_bound
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F)) (z : ℝ × E) :
    ‖A z‖ ≤ (1 + |(A.symm (1, 0)).1| + ‖(A.symm (1, 0)).2‖) * ‖z‖ := by
  let p : ℝ × E := A.symm (1, 0)
  change ‖A z‖ ≤ (1 + |p.1| + ‖p.2‖) * ‖z‖
  have hp : A p = (1, 0) := A.toLinearEquiv.apply_symm_apply (1, 0)
  have he : (A z).1 = p.1 * z.1 - inner ℝ p.2 z.2 := by
    have h := A.map_app z p
    rw [hp] at h
    simp only [lorentzForm_apply, inner_zero_left, one_mul, zero_sub] at h
    linarith
  have ht : ‖(A z).1‖ ≤ (|p.1| + ‖p.2‖) * ‖z‖ := by
    rw [he]
    calc
      ‖p.1 * z.1 - inner ℝ p.2 z.2‖ ≤ ‖p.1 * z.1‖ + ‖inner ℝ p.2 z.2‖ :=
        norm_sub_le _ _
      _ ≤ |p.1| * ‖z.1‖ + ‖p.2‖ * ‖z.2‖ := by
        rw [norm_mul, Real.norm_eq_abs p.1]
        exact add_le_add le_rfl (norm_inner_le_norm (𝕜 := ℝ) p.2 z.2)
      _ ≤ |p.1| * ‖z‖ + ‖p.2‖ * ‖z‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le z) (abs_nonneg p.1))
          (mul_le_mul_of_nonneg_left (norm_snd_le z) (norm_nonneg p.2))
      _ = (|p.1| + ‖p.2‖) * ‖z‖ := by ring
  have hq := A.map_app z z
  rw [lorentzForm_apply, lorentzForm_apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hq
  have hs : ‖(A z).2‖ ≤ ‖z.2‖ + ‖(A z).1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [Real.norm_eq_abs]
    nlinarith only [hq, sq_abs (A z).1, sq_nonneg z.1,
      mul_nonneg (norm_nonneg z.2) (abs_nonneg (A z).1)]
  apply norm_prod_le_iff.mpr
  constructor
  · nlinarith only [ht, norm_nonneg z]
  · calc
      ‖(A z).2‖ ≤ ‖z.2‖ + ‖(A z).1‖ := hs
      _ ≤ ‖z‖ + (|p.1| + ‖p.2‖) * ‖z‖ := add_le_add (norm_snd_le z) ht
      _ = (1 + |p.1| + ‖p.2‖) * ‖z‖ := by ring

def lorentzIsometryContinuousLinearEquiv
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F)) : (ℝ × E) ≃L[ℝ] (ℝ × F) :=
  A.toLinearEquiv.toContinuousLinearEquivOfBounds
    (1 + |(A.symm (1, 0)).1| + ‖(A.symm (1, 0)).2‖)
    (1 + |(A.symm.symm (1, 0)).1| + ‖(A.symm.symm (1, 0)).2‖)
    (lorentzIsometry_norm_bound A) (lorentzIsometry_norm_bound A.symm)

@[simp] theorem lorentzIsometryContinuousLinearEquiv_toLinearEquiv
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F)) :
    (lorentzIsometryContinuousLinearEquiv A).toLinearEquiv = A.toLinearEquiv := rfl

@[simp] theorem lorentzIsometryContinuousLinearEquiv_coe
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F)) :
    ⇑(lorentzIsometryContinuousLinearEquiv A) = A := rfl

theorem lorentzIsometryContinuousLinearEquiv_apply
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F)) (z : ℝ × E) :
    lorentzIsometryContinuousLinearEquiv A z = A z := rfl

@[simp] theorem lorentzIsometryContinuousLinearEquiv_symm_apply
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F)) (z : ℝ × F) :
    (lorentzIsometryContinuousLinearEquiv A).symm z = A.symm z := rfl

end DifferentialGeometry
