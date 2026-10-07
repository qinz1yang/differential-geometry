import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Metric
import Mathlib.Topology.UnitInterval

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def interpolationVector (t : unitInterval) (x y : Hyperboloid E) : ℝ × E :=
  (1 - (t : ℝ)) • (x.time, x.space) + (t : ℝ) • (y.time, y.space)

private theorem one_le_neg_lorentzForm_interpolationVector
    (t : unitInterval) (x y : Hyperboloid E) :
    1 ≤ -(lorentzForm E (interpolationVector t x y) (interpolationVector t x y)) := by
  have hx : lorentzForm E (x.time, x.space) (x.time, x.space) = -1 := by
    simp only [lorentzForm_apply, ← sq]
    linarith [x.time_sq_sub_inner_self]
  have hy : lorentzForm E (y.time, y.space) (y.time, y.space) = -1 := by
    simp only [lorentzForm_apply, ← sq]
    linarith [y.time_sq_sub_inner_self]
  have hxy : lorentzForm E (x.time, x.space) (y.time, y.space) ≤ -1 := by
    have h := Real.one_le_cosh (dist x y)
    rw [cosh_dist] at h
    simp only [lorentzForm_apply]
    linarith
  have hsym : lorentzForm E (y.time, y.space) (x.time, x.space) =
      lorentzForm E (x.time, x.space) (y.time, y.space) :=
    (lorentzForm_isSymm E).eq (y.time, y.space) (x.time, x.space)
  have ht : 0 ≤ (t : ℝ) * (1 - (t : ℝ)) :=
    mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)
  have hprod := mul_nonneg ht (show 0 ≤ -1 -
    lorentzForm E (x.time, x.space) (y.time, y.space) by linarith)
  simp only [interpolationVector, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hx, hy, hsym]
  nlinarith

private theorem interpolationVector_time_pos (t : unitInterval) (x y : Hyperboloid E) :
    0 < (interpolationVector t x y).1 := by
  change 0 < (1 - (t : ℝ)) * x.time + (t : ℝ) * y.time
  rcases eq_or_lt_of_le t.property.2 with ht | ht
  · simpa only [ht, sub_self, zero_mul, one_mul, zero_add] using y.time_pos
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht) x.time_pos)
      (mul_nonneg t.property.1 y.time_pos.le)

private def interpolationScale (t : unitInterval) (x y : Hyperboloid E) : ℝ :=
  Real.sqrt (-(lorentzForm E (interpolationVector t x y) (interpolationVector t x y)))

private theorem interpolationScale_pos (t : unitInterval) (x y : Hyperboloid E) :
    0 < interpolationScale t x y :=
  Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one
    (one_le_neg_lorentzForm_interpolationVector t x y))

private theorem interpolationScale_sq (t : unitInterval) (x y : Hyperboloid E) :
    interpolationScale t x y ^ 2 = (interpolationVector t x y).1 ^ 2 -
      inner ℝ (interpolationVector t x y).2 (interpolationVector t x y).2 := by
  rw [interpolationScale, Real.sq_sqrt
    (le_trans zero_le_one (one_le_neg_lorentzForm_interpolationVector t x y))]
  simp only [lorentzForm_apply, neg_sub, sq]

def interpolate (t : unitInterval) (x y : Hyperboloid E) : Hyperboloid E where
  time := (interpolationVector t x y).1 / interpolationScale t x y
  space := (interpolationScale t x y)⁻¹ • (interpolationVector t x y).2
  time_pos := div_pos (interpolationVector_time_pos t x y) (interpolationScale_pos t x y)
  time_sq_sub_inner_self := by
    have hn := (interpolationScale_pos t x y).ne'
    calc
      ((interpolationVector t x y).1 / interpolationScale t x y) ^ 2 -
          inner ℝ ((interpolationScale t x y)⁻¹ • (interpolationVector t x y).2)
            ((interpolationScale t x y)⁻¹ • (interpolationVector t x y).2) =
          ((interpolationVector t x y).1 ^ 2 -
            inner ℝ (interpolationVector t x y).2 (interpolationVector t x y).2) /
              interpolationScale t x y ^ 2 := by
        simp only [real_inner_smul_left, real_inner_smul_right, div_eq_mul_inv, mul_pow,
          inv_pow]
        ring
      _ = 1 := by rw [← interpolationScale_sq]; exact div_self (pow_ne_zero 2 hn)

theorem interpolate_coordinates (t : unitInterval) (x y : Hyperboloid E) :
    let z := (1 - (t : ℝ)) • (x.time, x.space) + (t : ℝ) • (y.time, y.space)
    ((interpolate t x y).time, (interpolate t x y).space) =
      (Real.sqrt (-(lorentzForm E z z)))⁻¹ • z := by
  apply Prod.ext
  · change (interpolationVector t x y).1 / interpolationScale t x y =
      (interpolationScale t x y)⁻¹ * (interpolationVector t x y).1
    rw [div_eq_mul_inv, mul_comm]
  · rfl

@[simp] theorem interpolate_zero (x y : Hyperboloid E) : interpolate 0 x y = x := by
  ext
  simp [interpolate, interpolationScale, interpolationVector, lorentzForm_apply,
    ← sq, x.time_sq]

@[simp] theorem interpolate_one (x y : Hyperboloid E) : interpolate 1 x y = y := by
  ext
  simp [interpolate, interpolationScale, interpolationVector, lorentzForm_apply,
    ← sq, y.time_sq]

theorem continuous_interpolate : Continuous
    (fun q : unitInterval × (Hyperboloid E × Hyperboloid E) =>
      interpolate q.1 q.2.1 q.2.2) := by
  have ht : Continuous (fun q : unitInterval × (Hyperboloid E × Hyperboloid E) =>
      (q.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun q : unitInterval × (Hyperboloid E × Hyperboloid E) =>
      (q.2.1.time, q.2.1.space)) :=
    (continuous_time.prodMk continuous_space).comp (continuous_fst.comp continuous_snd)
  have hy : Continuous (fun q : unitInterval × (Hyperboloid E × Hyperboloid E) =>
      (q.2.2.time, q.2.2.space)) :=
    (continuous_time.prodMk continuous_space).comp (continuous_snd.comp continuous_snd)
  have hv : Continuous (fun q : unitInterval × (Hyperboloid E × Hyperboloid E) =>
      interpolationVector q.1 q.2.1 q.2.2) :=
    ((continuous_const.sub ht).smul hx).add (ht.smul hy)
  have hd : Continuous (fun q : unitInterval × (Hyperboloid E × Hyperboloid E) =>
      interpolationScale q.1 q.2.1 q.2.2) := by
    exact ((hv.snd.inner hv.snd).sub (hv.fst.mul hv.fst)).neg.sqrt
  have hn (q : unitInterval × (Hyperboloid E × Hyperboloid E)) :
      interpolationScale q.1 q.2.1 q.2.2 ≠ 0 :=
    (interpolationScale_pos q.1 q.2.1 q.2.2).ne'
  apply continuous_induced_rng.2
  exact (hv.fst.div hd hn).prodMk ((hd.inv₀ hn).smul hv.snd)

end DifferentialGeometry.Hyperboloid
