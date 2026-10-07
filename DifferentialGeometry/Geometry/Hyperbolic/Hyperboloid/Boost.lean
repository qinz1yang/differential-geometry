import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.LorentzIsometry

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def boostLinear (x : Hyperboloid E) : (ℝ × E) →ₗ[ℝ] ℝ × E :=
  let t := LinearMap.fst ℝ ℝ E
  let v := LinearMap.snd ℝ ℝ E
  let i := (innerₗ E x.space).comp v
  (x.time • t + i).prod (v + (t + (x.time + 1)⁻¹ • i).smulRight x.space)

private theorem boostLinear_apply (x : Hyperboloid E) (z : ℝ × E) :
    boostLinear x z =
      (x.time * z.1 + inner ℝ x.space z.2,
        z.2 + (z.1 + inner ℝ x.space z.2 / (x.time + 1)) • x.space) := by
  change (x.time * z.1 + inner ℝ x.space z.2,
    z.2 + (z.1 + (x.time + 1)⁻¹ * inner ℝ x.space z.2) • x.space) = _
  rw [div_eq_mul_inv, mul_comm (x.time + 1)⁻¹]

private theorem boostLinear_preserves (x : Hyperboloid E) (z w : ℝ × E) :
    lorentzForm E (boostLinear x z) (boostLinear x w) = lorentzForm E z w := by
  have hd : x.time + 1 ≠ 0 := ne_of_gt (by linarith [x.time_pos])
  have hs : inner ℝ x.space x.space = x.time ^ 2 - 1 := by
    linarith [x.time_sq_sub_inner_self]
  simp only [boostLinear_apply, lorentzForm_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm z.2 x.space,
    hs]
  field_simp [hd]
  ring

private theorem time_ofSpace_neg (x : Hyperboloid E) :
    (ofSpace (-x.space)).time = x.time := by
  simp only [time_ofSpace, norm_neg, x.time_eq_sqrt]

private theorem boostLinear_neg_leftInverse (x : Hyperboloid E) (z : ℝ × E) :
    boostLinear (ofSpace (-x.space)) (boostLinear x z) = z := by
  have hd : x.time + 1 ≠ 0 := ne_of_gt (by linarith [x.time_pos])
  have hs : inner ℝ x.space x.space = x.time ^ 2 - 1 := by
    linarith [x.time_sq_sub_inner_self]
  have hc : x.time * z.1 + inner ℝ x.space z.2 +
      inner ℝ (-x.space)
        (z.2 + (z.1 + inner ℝ x.space z.2 / (x.time + 1)) • x.space) /
          (x.time + 1) = z.1 + inner ℝ x.space z.2 / (x.time + 1) := by
    simp only [inner_neg_left, inner_add_right, real_inner_smul_right, hs]
    field_simp [hd]
    ring
  apply Prod.ext
  · simp only [boostLinear_apply, time_ofSpace_neg, space_ofSpace, inner_neg_left,
      inner_add_right, real_inner_smul_right, hs]
    field_simp [hd]
    ring
  · simp only [boostLinear_apply, time_ofSpace_neg, space_ofSpace]
    rw [hc, smul_neg, add_neg_cancel_right]

def lorentzBoost (x : Hyperboloid E) :
    (lorentzForm E).IsometryEquiv (lorentzForm E) where
  toLinearEquiv :=
    { boostLinear x with
      invFun := boostLinear (ofSpace (-x.space))
      left_inv := boostLinear_neg_leftInverse x
      right_inv := by
        intro z
        change boostLinear x (boostLinear (ofSpace (-x.space)) z) = z
        simpa only [space_ofSpace, neg_neg, ofSpace_space] using
          boostLinear_neg_leftInverse (ofSpace (-x.space)) z }
  map_app' := boostLinear_preserves x

theorem lorentzBoost_apply (x : Hyperboloid E) (z : ℝ × E) :
    lorentzBoost x z =
      (x.time * z.1 + inner ℝ x.space z.2,
        z.2 + (z.1 + inner ℝ x.space z.2 / (x.time + 1)) • x.space) :=
  boostLinear_apply x z

@[simp] theorem lorentzBoost_symm (x : Hyperboloid E) :
    (lorentzBoost x).symm = lorentzBoost (ofSpace (-x.space)) := by
  apply DFunLike.ext
  intro z
  rfl

private theorem lorentzBoost_origin_time_pos (x : Hyperboloid E) :
    0 < (lorentzBoost x (1, 0)).1 := by
  change 0 < (boostLinear x (1, 0)).1
  simpa only [boostLinear_apply, inner_zero_right, mul_one, add_zero] using x.time_pos

def boost (x : Hyperboloid E) : Hyperboloid E ≃ᵢ Hyperboloid E :=
  lorentzIsometryEquiv (lorentzBoost x) (lorentzBoost_origin_time_pos x)

theorem boost_coordinates (x y : Hyperboloid E) :
    ((boost x y).time, (boost x y).space) =
      (x.time * y.time + inner ℝ x.space y.space,
        y.space + (y.time + inner ℝ x.space y.space / (x.time + 1)) • x.space) := by
  exact (lorentzIsometryEquiv_coordinates (lorentzBoost x)
    (lorentzBoost_origin_time_pos x) y).trans (lorentzBoost_apply x (y.time, y.space))

@[simp] theorem boost_origin (x : Hyperboloid E) : boost x origin = x := by
  apply Hyperboloid.ext
  simpa using congrArg Prod.snd (boost_coordinates x origin)

@[simp] theorem boost_symm (x : Hyperboloid E) :
    (boost x).symm = boost (ofSpace (-x.space)) := by
  apply IsometryEquiv.ext
  intro y
  apply Hyperboloid.ext
  rfl

end DifferentialGeometry.Hyperboloid
