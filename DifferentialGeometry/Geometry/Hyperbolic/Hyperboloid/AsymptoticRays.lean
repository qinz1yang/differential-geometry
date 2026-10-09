import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.GeodesicBoundary

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_space_sub_eq_time_sub (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    ‖x.space - v.2‖ = x.time - v.1 := by
  have hp := time_sub_fst_pos x v hv ho
  have hn := norm_geodesicLine_backward_endpoint x v hv ho
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)] at hn
  apply mul_left_cancel₀ (inv_ne_zero hp.ne')
  rw [inv_mul_cancel₀ hp.ne']
  exact hn

private theorem lorentz_forward_eq_zero (x y : Hyperboloid E) (v w : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (hw : lorentzForm E w w = 1) (how : lorentzForm E (y.time, y.space) w = 0)
    (h : (x.time + v.1)⁻¹ • (x.space + v.2) =
      (y.time + w.1)⁻¹ • (y.space + w.2)) :
    lorentzForm E ((x.time, x.space) + v) ((y.time, y.space) + w) = 0 := by
  have hp := (time_add_fst_pos x v hv ho).ne'
  have hq := (time_add_fst_pos y w hw how).ne'
  have hi : inner ℝ ((x.time + v.1)⁻¹ • (x.space + v.2))
      ((y.time + w.1)⁻¹ • (y.space + w.2)) = 1 := by
    rw [← h, real_inner_self_eq_norm_sq, norm_geodesicLine_forward_endpoint x v hv ho]
    norm_num
  rw [real_inner_smul_left, real_inner_smul_right] at hi
  have he : inner ℝ (x.space + v.2) (y.space + w.2) =
      (x.time + v.1) * (y.time + w.1) := by
    field_simp at hi
    exact hi
  exact sub_eq_zero.mpr he

private theorem lorentz_backward_nonpos (x y : Hyperboloid E) (v w : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (hw : lorentzForm E w w = 1) (how : lorentzForm E (y.time, y.space) w = 0) :
    lorentzForm E ((x.time, x.space) - v) ((y.time, y.space) - w) ≤ 0 := by
  have h := real_inner_le_norm (x.space - v.2) (y.space - w.2)
  rw [norm_space_sub_eq_time_sub x v hv ho, norm_space_sub_eq_time_sub y w hw how] at h
  exact sub_nonpos.mpr h

theorem dist_geodesicLine_le_of_forward_endpoint_eq
    (x y : Hyperboloid E) (v w : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (hw : lorentzForm E w w = 1) (how : lorentzForm E (y.time, y.space) w = 0)
    (h : (x.time + v.1)⁻¹ • (x.space + v.2) =
      (y.time + w.1)⁻¹ • (y.space + w.2)) {t : ℝ} (ht : 0 ≤ t) :
    dist (geodesicLine x v hv ho t) (geodesicLine y w hw how t) ≤ dist x y := by
  let X : ℝ × E := (x.time, x.space)
  let Y : ℝ × E := (y.time, y.space)
  have hf : lorentzForm E X Y + lorentzForm E X w +
      lorentzForm E v Y + lorentzForm E v w = 0 := by
    have hf := lorentz_forward_eq_zero x y v w hv ho hw how h
    simp only [map_add, LinearMap.add_apply] at hf
    dsimp only [X, Y]
    linarith
  have hb : lorentzForm E X Y - lorentzForm E X w -
      lorentzForm E v Y + lorentzForm E v w ≤ 0 := by
    have hb := lorentz_backward_nonpos x y v w hv ho hw how
    simp only [map_sub, LinearMap.sub_apply] at hb
    dsimp only [X, Y]
    linarith
  have hh : 0 ≤ lorentzForm E X w + lorentzForm E v Y := by linarith
  have hs : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht
  have he : Real.sinh t ^ 2 - Real.cosh t * Real.sinh t ≤ 0 := by
    nlinarith [Real.sinh_lt_cosh (x := t)]
  have hprod := mul_nonpos_of_nonpos_of_nonneg he hh
  have hcosh := Real.cosh_sq_sub_sinh_sq t
  have hl : lorentzForm E (Real.cosh t • X + Real.sinh t • v)
      (Real.cosh t • Y + Real.sinh t • w) = lorentzForm E X Y +
      (Real.cosh t * Real.sinh t - Real.sinh t ^ 2) *
        (lorentzForm E X w + lorentzForm E v Y) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have hvw : lorentzForm E v w =
        -(lorentzForm E X Y + lorentzForm E X w + lorentzForm E v Y) := by linarith
    rw [hvw]
    have hid := congrArg (fun r : ℝ => r * lorentzForm E X Y) hcosh
    nlinarith only [hid]
  have hdist : Real.cosh (dist (geodesicLine x v hv ho t) (geodesicLine y w hw how t)) =
      -lorentzForm E (Real.cosh t • X + Real.sinh t • v)
        (Real.cosh t • Y + Real.sinh t • w) := by
    rw [cosh_dist]
    change (geodesicLine x v hv ho t).time * (geodesicLine y w hw how t).time -
      inner ℝ (geodesicLine x v hv ho t).space (geodesicLine y w hw how t).space =
      -(inner ℝ (geodesicLine x v hv ho t).space (geodesicLine y w hw how t).space -
        (geodesicLine x v hv ho t).time * (geodesicLine y w hw how t).time)
    ring
  have hbase : Real.cosh (dist x y) = -lorentzForm E X Y := by
    rw [cosh_dist]
    change x.time * y.time - inner ℝ x.space y.space =
      -(inner ℝ x.space y.space - x.time * y.time)
    ring
  have hle : Real.cosh (dist (geodesicLine x v hv ho t) (geodesicLine y w hw how t)) ≤
      Real.cosh (dist x y) := by rw [hdist, hbase, hl]; nlinarith
  simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hle

end DifferentialGeometry.Hyperboloid
