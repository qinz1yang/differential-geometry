import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Metric
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private def ofLorentzVector (v : ℝ × E) (ht : 0 < v.1)
    (hn : lorentzForm E v v = -1) : Hyperboloid E where
  time := v.1
  space := v.2
  time_pos := ht
  time_sq_sub_inner_self := by
    rw [lorentzForm_apply] at hn
    nlinarith

private theorem lorentz_norm_image
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F)) (x : Hyperboloid E) :
    lorentzForm F (A (x.time, x.space)) (A (x.time, x.space)) = -1 := by
  rw [A.map_app, lorentzForm_apply]
  nlinarith [x.time_sq_sub_inner_self]

private theorem lorentz_origin_image_norm
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F)) :
    lorentzForm F (A (1, 0)) (A (1, 0)) = -1 := by
  rw [A.map_app]
  simp [lorentzForm_apply]

private theorem lorentz_image_time_pos
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F))
    (hA : 0 < (A (1, 0)).1) (x : Hyperboloid E) :
    0 < (A (x.time, x.space)).1 := by
  let v := A (x.time, x.space)
  let o := A (1, 0)
  have hv : lorentzForm F v v = -1 := lorentz_norm_image A x
  have hv0 : v.1 ≠ 0 := by
    intro hzero
    rw [lorentzForm_apply, real_inner_self_eq_norm_sq, hzero] at hv
    nlinarith [sq_nonneg ‖v.2‖]
  rcases lt_or_gt_of_ne hv0 with hvneg | hvpos
  · have hn : lorentzForm F (-v) (-v) = -1 := by
      simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hv
    let u := ofLorentzVector (-v) (by simpa using neg_pos.mpr hvneg) hn
    let w := ofLorentzVector o hA (lorentz_origin_image_norm A)
    have h := Real.one_le_cosh (dist u w)
    rw [cosh_dist] at h
    change 1 ≤ (-v).1 * o.1 - inner ℝ (-v).2 o.2 at h
    have hp : lorentzForm F v o = -x.time := by
      change lorentzForm F (A (x.time, x.space)) (A (1, 0)) = -x.time
      rw [A.map_app]
      simp [lorentzForm_apply]
    rw [lorentzForm_apply] at hp
    simp only [Prod.fst_neg, Prod.snd_neg, inner_neg_left] at h
    nlinarith [x.time_pos]
  · exact hvpos

private theorem lorentz_inverse_origin_time
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F)) :
    (A.symm (1, 0)).1 = (A (1, 0)).1 := by
  have h := A.map_app (1, 0) (A.symm (1, 0))
  have hi : A (A.symm (1, 0)) = (1, 0) := A.toLinearEquiv.apply_symm_apply (1, 0)
  rw [hi] at h
  simp only [lorentzForm_apply, inner_zero_left, inner_zero_right, one_mul, mul_one] at h
  linarith

private def lorentzMap
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F))
    (hA : 0 < (A (1, 0)).1) (x : Hyperboloid E) : Hyperboloid F :=
  ofLorentzVector (A (x.time, x.space)) (lorentz_image_time_pos A hA x)
    (lorentz_norm_image A x)

def lorentzIsometryEquiv
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F))
    (hA : 0 < (A (1, 0)).1) : Hyperboloid E ≃ᵢ Hyperboloid F where
  toFun := lorentzMap A hA
  invFun := lorentzMap A.symm (by rwa [lorentz_inverse_origin_time])
  left_inv x := by
    apply Hyperboloid.ext
    exact congrArg Prod.snd (A.toLinearEquiv.symm_apply_apply (x.time, x.space))
  right_inv y := by
    apply Hyperboloid.ext
    exact congrArg Prod.snd (A.toLinearEquiv.apply_symm_apply (y.time, y.space))
  isometry_toFun := isometry_iff_dist_eq.mpr fun x y => by
    rw [dist_eq_arcosh, dist_eq_arcosh]
    apply congrArg Real.arcosh
    have h := A.map_app (y.time, y.space) (x.time, x.space)
    rw [lorentzForm_apply, lorentzForm_apply] at h
    change (A (x.time, x.space)).1 * (A (y.time, y.space)).1 -
      inner ℝ (A (x.time, x.space)).2 (A (y.time, y.space)).2 =
        x.time * y.time - inner ℝ x.space y.space
    linarith

@[simp] theorem lorentzIsometryEquiv_coordinates
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F))
    (hA : 0 < (A (1, 0)).1) (x : Hyperboloid E) :
    ((lorentzIsometryEquiv A hA x).time, (lorentzIsometryEquiv A hA x).space) =
      A (x.time, x.space) := rfl

@[simp] theorem lorentzIsometryEquiv_symm_coordinates
    (A : (lorentzForm E).IsometryEquiv (lorentzForm F))
    (hA : 0 < (A (1, 0)).1) (y : Hyperboloid F) :
    (((lorentzIsometryEquiv A hA).symm y).time,
      ((lorentzIsometryEquiv A hA).symm y).space) = A.symm (y.time, y.space) := rfl

end DifferentialGeometry.Hyperboloid
