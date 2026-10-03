import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Geodesic
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Klein

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem abs_fst_lt_time (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    |v.1| < x.time := by
  have hx : lorentzForm E (x.time, x.space) (x.time, x.space) ≤ -1 := by
    rw [lorentzForm_apply]
    nlinarith [x.time_sq_sub_inner_self]
  have hn := norm_snd_sq_le_mul_lorentzForm_self_of_orthogonal hx ho
  rw [hv] at hn
  have hv' : ‖v.2‖ ^ 2 - v.1 * v.1 = 1 := by
    simpa only [lorentzForm_apply, real_inner_self_eq_norm_sq] using hv
  nlinarith [sq_abs v.1, abs_nonneg v.1, x.time_pos]

theorem time_add_fst_pos (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    0 < x.time + v.1 := by
  have h := abs_fst_lt_time x v hv ho
  linarith [neg_abs_le v.1]

theorem time_sub_fst_pos (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    0 < x.time - v.1 := by
  have h := abs_fst_lt_time x v hv ho
  linarith [le_abs_self v.1]

theorem norm_geodesicLine_forward_endpoint (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    ‖(x.time + v.1)⁻¹ • (x.space + v.2)‖ = 1 := by
  have hpos := time_add_fst_pos x v hv ho
  have hnorm : ‖x.space + v.2‖ = x.time + v.1 := by
    have hv' : ‖v.2‖ ^ 2 - v.1 * v.1 = 1 := by
      simpa only [lorentzForm_apply, real_inner_self_eq_norm_sq] using hv
    have ho' : inner ℝ x.space v.2 = x.time * v.1 := sub_eq_zero.mp ho
    have hs := norm_add_sq_real x.space v.2
    rw [ho'] at hs
    nlinarith [x.time_sq, norm_nonneg (x.space + v.2)]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), hnorm,
    inv_mul_cancel₀ hpos.ne']

theorem norm_geodesicLine_backward_endpoint (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    ‖(x.time - v.1)⁻¹ • (x.space - v.2)‖ = 1 := by
  have hv' : lorentzForm E (-v) (-v) = 1 := by
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hv
  have ho' : lorentzForm E (x.time, x.space) (-v) = 0 := by
    rw [map_neg, ho, neg_zero]
  simpa only [Prod.fst_neg, Prod.snd_neg, ← sub_eq_add_neg] using
    norm_geodesicLine_forward_endpoint x (-v) hv' ho'

theorem geodesicLine_endpoints_ne (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    (x.time + v.1)⁻¹ • (x.space + v.2) ≠ (x.time - v.1)⁻¹ • (x.space - v.2) := by
  intro h
  have hp := (time_add_fst_pos x v hv ho).ne'
  have hm := (time_sub_fst_pos x v hv ho).ne'
  have hc := congrArg (fun z : E => ((x.time + v.1) * (x.time - v.1)) • z) h
  simp only [smul_smul] at hc
  have ha : ((x.time + v.1) * (x.time - v.1)) * (x.time + v.1)⁻¹ = x.time - v.1 := by
    field_simp
  have hb : ((x.time + v.1) * (x.time - v.1)) * (x.time - v.1)⁻¹ = x.time + v.1 := by
    field_simp
  rw [ha, hb] at hc
  have hd : (2 * x.time) • v.2 = (2 * v.1) • x.space := calc
    (2 * x.time) • v.2 =
        (x.time - v.1) • (x.space + v.2) - (x.time + v.1) • (x.space - v.2) +
          (2 * v.1) • x.space := by module
    _ = (2 * v.1) • x.space := by rw [hc, sub_self, zero_add]
  have hi := congrArg (fun z : E => inner ℝ x.space z) hd
  simp only [real_inner_smul_right] at hi
  have ho' : inner ℝ x.space v.2 = x.time * v.1 := sub_eq_zero.mp ho
  have hself : inner ℝ x.space x.space = x.time ^ 2 - 1 := by
    linarith [x.time_sq_sub_inner_self]
  rw [ho', hself] at hi
  have ht : v.1 = 0 := by nlinarith
  rw [ht, mul_zero, zero_smul] at hd
  have hs : v.2 = 0 := (smul_eq_zero.mp hd).resolve_left (mul_ne_zero (by norm_num) x.time_pos.ne')
  rw [lorentzForm_apply, ht, hs] at hv
  simp at hv

theorem kleinHomeomorph_geodesicLine (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) (t : ℝ) :
    (kleinHomeomorph (geodesicLine x v hv ho t) : E) =
      (x.time + Real.tanh t * v.1)⁻¹ • (x.space + Real.tanh t • v.2) := by
  have hc := (Real.cosh_pos t).ne'
  have ht : Real.cosh t * x.time + Real.sinh t * v.1 =
      Real.cosh t * (x.time + Real.tanh t * v.1) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hs : Real.cosh t • x.space + Real.sinh t • v.2 =
      Real.cosh t • (x.space + Real.tanh t • v.2) := by
    rw [smul_add, smul_smul, Real.tanh_eq_sinh_div_cosh]
    congr 1
    field_simp
  rw [kleinHomeomorph_apply_coe, geodesicLine_time, geodesicLine_space, ht, hs,
    smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]

private theorem tanh_ratio (t : ℝ) :
    Real.tanh t = (1 - Real.exp (-t) ^ 2) / (1 + Real.exp (-t) ^ 2) := by
  rw [Real.tanh_eq, Real.exp_neg]
  field_simp

private theorem tendsto_tanh_atTop :
    Filter.Tendsto Real.tanh Filter.atTop (𝓝 (1 : ℝ)) := by
  have h : Filter.Tendsto (fun t : ℝ => Real.exp (-t) ^ 2) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.pow 2
  have hq := ((tendsto_const_nhds (x := (1 : ℝ))).sub h).div (tendsto_const_nhds.add h)
    (by norm_num : (1 : ℝ) + 0 ≠ 0)
  convert hq using 1
  · funext t
    exact tanh_ratio t
  · norm_num

private theorem tendsto_tanh_atBot :
    Filter.Tendsto Real.tanh Filter.atBot (𝓝 (-1 : ℝ)) := by
  simpa only [Function.comp_def, Real.tanh_neg, neg_neg] using
    tendsto_tanh_atTop.neg.comp Filter.tendsto_neg_atBot_atTop

theorem tendsto_kleinHomeomorph_geodesicLine_atTop (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    Filter.Tendsto (fun t => (kleinHomeomorph (geodesicLine x v hv ho t) : E)) Filter.atTop
      (𝓝 ((x.time + v.1)⁻¹ • (x.space + v.2))) := by
  have hd : Filter.Tendsto (fun t => x.time + Real.tanh t * v.1) Filter.atTop
      (𝓝 (x.time + v.1)) := by
    simpa using tendsto_const_nhds.add (tendsto_tanh_atTop.mul_const v.1)
  have hs : Filter.Tendsto (fun t => x.space + Real.tanh t • v.2) Filter.atTop
      (𝓝 (x.space + v.2)) := by
    simpa using tendsto_const_nhds.add (tendsto_tanh_atTop.smul_const v.2)
  simpa only [kleinHomeomorph_geodesicLine] using
    (hd.inv₀ (time_add_fst_pos x v hv ho).ne').smul hs

theorem tendsto_kleinHomeomorph_geodesicLine_atBot (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    Filter.Tendsto (fun t => (kleinHomeomorph (geodesicLine x v hv ho t) : E)) Filter.atBot
      (𝓝 ((x.time - v.1)⁻¹ • (x.space - v.2))) := by
  have hd : Filter.Tendsto (fun t => x.time + Real.tanh t * v.1) Filter.atBot
      (𝓝 (x.time - v.1)) := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using
      tendsto_const_nhds.add (tendsto_tanh_atBot.mul_const v.1)
  have hs : Filter.Tendsto (fun t => x.space + Real.tanh t • v.2) Filter.atBot
      (𝓝 (x.space - v.2)) := by
    simpa only [neg_one_smul, ← sub_eq_add_neg] using
      tendsto_const_nhds.add (tendsto_tanh_atBot.smul_const v.2)
  simpa only [kleinHomeomorph_geodesicLine] using
    (hd.inv₀ (time_sub_fst_pos x v hv ho).ne').smul hs

end DifferentialGeometry.Hyperboloid
