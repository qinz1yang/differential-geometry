import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Geodesic
import Mathlib.Analysis.SpecialFunctions.Arsinh

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def normalPart (e : E) (x : Hyperboloid E) : E :=
  x.space - inner ℝ x.space e • e

private def normalScale (e : E) (x : Hyperboloid E) : ℝ :=
  Real.sqrt (1 + ‖normalPart e x‖ ^ 2)

private theorem normalScale_pos (e : E) (x : Hyperboloid E) : 0 < normalScale e x :=
  Real.sqrt_pos.mpr (by positivity)

private theorem normalScale_sq (e : E) (x : Hyperboloid E) :
    normalScale e x ^ 2 = 1 + ‖normalPart e x‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem normalPart_inner (e : E) (he : ‖e‖ = 1) (x y : Hyperboloid E) :
    inner ℝ (normalPart e x) (normalPart e y) =
      inner ℝ x.space y.space - inner ℝ x.space e * inner ℝ y.space e := by
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hsym : inner ℝ e y.space = inner ℝ y.space e := real_inner_comm _ _
  simp only [normalPart, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hee, hsym]
  ring

private theorem time_sq_eq_normalScale_sq_add (e : E) (he : ‖e‖ = 1) (x : Hyperboloid E) :
    x.time ^ 2 = normalScale e x ^ 2 + (inner ℝ x.space e) ^ 2 := by
  have h := normalPart_inner e he x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [normalScale_sq, time_sq]
  nlinarith

def lineProjection (e : E) (he : ‖e‖ = 1) (x : Hyperboloid E) : Hyperboloid E where
  time := x.time / normalScale e x
  space := (inner ℝ x.space e / normalScale e x) • e
  time_pos := div_pos x.time_pos (normalScale_pos e x)
  time_sq_sub_inner_self := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    have h := time_sq_eq_normalScale_sq_add e he x
    field_simp [(normalScale_pos e x).ne']
    nlinarith

theorem lineProjection_time (e : E) (he : ‖e‖ = 1) (x : Hyperboloid E) :
    (lineProjection e he x).time =
      x.time / Real.sqrt (1 + ‖x.space - inner ℝ x.space e • e‖ ^ 2) := rfl

theorem lineProjection_space (e : E) (he : ‖e‖ = 1) (x : Hyperboloid E) :
    (lineProjection e he x).space =
      (inner ℝ x.space e / Real.sqrt (1 + ‖x.space - inner ℝ x.space e • e‖ ^ 2)) • e := rfl

theorem cosh_dist_lineProjection (e : E) (he : ‖e‖ = 1) (x : Hyperboloid E) :
    Real.cosh (dist x (lineProjection e he x)) =
      Real.sqrt (1 + ‖x.space - inner ℝ x.space e • e‖ ^ 2) := by
  rw [cosh_dist]
  change x.time * (x.time / normalScale e x) -
    inner ℝ x.space ((inner ℝ x.space e / normalScale e x) • e) = normalScale e x
  rw [real_inner_smul_right]
  have h := time_sq_eq_normalScale_sq_add e he x
  field_simp [(normalScale_pos e x).ne']
  nlinarith

theorem lineProjection_mem_range (e : E) (he : ‖e‖ = 1) (x : Hyperboloid E) :
    lineProjection e he x ∈ Set.range (geodesicLine origin (0, e)
      (by simp [lorentzForm_apply, he])
      (by simp [lorentzForm_apply])) := by
  refine ⟨Real.arsinh (inner ℝ x.space e / normalScale e x), ?_⟩
  apply ext
  simp only [geodesicLine_space, origin_space, smul_zero, zero_add, Real.sinh_arsinh]
  rfl

private theorem cosh_dist_eq_mul_of_space (e : E) (he : ‖e‖ = 1) (x q : Hyperboloid E)
    (a : ℝ) (hq : q.space = a • e) :
    Real.cosh (dist x q) = normalScale e x * Real.cosh (dist (lineProjection e he x) q) := by
  rw [cosh_dist, cosh_dist]
  change x.time * q.time - inner ℝ x.space q.space =
    normalScale e x * (x.time / normalScale e x * q.time -
      inner ℝ ((inner ℝ x.space e / normalScale e x) • e) q.space)
  rw [hq, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, he]
  field_simp [(normalScale_pos e x).ne']

theorem cosh_dist_eq_mul_cosh_dist_lineProjection (e : E) (he : ‖e‖ = 1)
    (x q : Hyperboloid E) (hq : q ∈ Set.range (geodesicLine origin (0, e)
      (by simp [lorentzForm_apply, he])
      (by simp [lorentzForm_apply]))) :
    Real.cosh (dist x q) = Real.cosh (dist x (lineProjection e he x)) *
      Real.cosh (dist (lineProjection e he x) q) := by
  rw [cosh_dist_lineProjection]
  obtain ⟨t, rfl⟩ := hq
  apply cosh_dist_eq_mul_of_space e he x _ (Real.sinh t)
  simp

theorem dist_lineProjection_le (e : E) (he : ‖e‖ = 1) (x q : Hyperboloid E)
    (hq : q ∈ Set.range (geodesicLine origin (0, e)
      (by simp [lorentzForm_apply, he])
      (by simp [lorentzForm_apply]))) :
    dist x (lineProjection e he x) ≤ dist x q := by
  have h : Real.cosh (dist x (lineProjection e he x)) ≤ Real.cosh (dist x q) := by
    rw [cosh_dist_eq_mul_cosh_dist_lineProjection e he x q hq]
    nlinarith [Real.one_le_cosh (dist (lineProjection e he x) q),
      Real.cosh_pos (dist x (lineProjection e he x))]
  simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp h

theorem eq_lineProjection_of_dist_le (e : E) (he : ‖e‖ = 1) (x q : Hyperboloid E)
    (hq : q ∈ Set.range (geodesicLine origin (0, e)
      (by simp [lorentzForm_apply, he])
      (by simp [lorentzForm_apply]))) (hd : dist x q ≤ dist x (lineProjection e he x)) :
    q = lineProjection e he x := by
  have hd' := Real.cosh_le_cosh.mpr (show |dist x q| ≤ |dist x (lineProjection e he x)| by
    simpa only [abs_of_nonneg dist_nonneg] using hd)
  rw [cosh_dist_eq_mul_cosh_dist_lineProjection e he x q hq] at hd'
  have hc : Real.cosh (dist (lineProjection e he x) q) = 1 := by
    nlinarith [Real.one_le_cosh (dist (lineProjection e he x) q),
      Real.cosh_pos (dist x (lineProjection e he x))]
  have hzero : dist (lineProjection e he x) q = 0 := by
    rw [← Real.arcosh_cosh dist_nonneg, hc, Real.arcosh_zero]
  exact (dist_eq_zero.mp hzero).symm

private theorem cosh_dist_projection_pair (e : E) (he : ‖e‖ = 1) (x y : Hyperboloid E) :
    Real.cosh (dist (lineProjection e he x) (lineProjection e he y)) =
      (x.time * y.time - inner ℝ x.space e * inner ℝ y.space e) /
        (normalScale e x * normalScale e y) := by
  rw [cosh_dist]
  change x.time / normalScale e x * (y.time / normalScale e y) -
    inner ℝ ((inner ℝ x.space e / normalScale e x) • e)
      ((inner ℝ y.space e / normalScale e y) • e) = _
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
  field_simp [(normalScale_pos e x).ne', (normalScale_pos e y).ne']

private theorem cosh_dist_decomposition (e : E) (he : ‖e‖ = 1) (x y : Hyperboloid E) :
    Real.cosh (dist x y) = normalScale e x * normalScale e y *
      (Real.cosh (dist (lineProjection e he x) (lineProjection e he y)) - 1) +
      Real.cosh (dist (ofSpace (normalPart e x)) (ofSpace (normalPart e y))) := by
  rw [cosh_dist_projection_pair, cosh_dist, cosh_dist, time_ofSpace, time_ofSpace,
    space_ofSpace, space_ofSpace, normalPart_inner e he x y]
  change x.time * y.time - inner ℝ x.space y.space =
    normalScale e x * normalScale e y *
      ((x.time * y.time - inner ℝ x.space e * inner ℝ y.space e) /
        (normalScale e x * normalScale e y) - 1) +
      (normalScale e x * normalScale e y -
        (inner ℝ x.space y.space - inner ℝ x.space e * inner ℝ y.space e))
  field_simp [(normalScale_pos e x).ne', (normalScale_pos e y).ne']
  ring

theorem cosh_dist_lineProjection_sub_one_le (e : E) (he : ‖e‖ = 1) (x y : Hyperboloid E) :
    Real.cosh (dist (lineProjection e he x) (lineProjection e he y)) - 1 ≤
      (Real.cosh (dist x y) - 1) /
        (Real.cosh (dist x (lineProjection e he x)) *
          Real.cosh (dist y (lineProjection e he y))) := by
  rw [cosh_dist_lineProjection, cosh_dist_lineProjection]
  change Real.cosh (dist (lineProjection e he x) (lineProjection e he y)) - 1 ≤
    (Real.cosh (dist x y) - 1) / (normalScale e x * normalScale e y)
  apply (le_div_iff₀ (mul_pos (normalScale_pos e x) (normalScale_pos e y))).mpr
  have h := cosh_dist_decomposition e he x y
  have hc := Real.one_le_cosh (dist (ofSpace (normalPart e x)) (ofSpace (normalPart e y)))
  nlinarith

theorem dist_lineProjection_le_two_mul_exp (e : E) (he : ‖e‖ = 1) (x y : Hyperboloid E) :
    dist (lineProjection e he x) (lineProjection e he y) ≤
      2 * Real.exp ((dist x y - dist x (lineProjection e he x) -
        dist y (lineProjection e he y)) / 2) := by
  let p := dist (lineProjection e he x) (lineProjection e he y)
  let d := dist x y
  let a := dist x (lineProjection e he x)
  let b := dist y (lineProjection e he y)
  change p ≤ 2 * Real.exp ((d - a - b) / 2)
  have hp0 : 0 ≤ p := dist_nonneg
  have hd0 : 0 ≤ d := dist_nonneg
  have hp : p ^ 2 / 2 ≤ Real.cosh p - 1 := by
    have hh : 0 ≤ p / 2 := div_nonneg hp0 (by norm_num)
    have hs := Real.self_le_sinh_iff.mpr hh
    have hs0 := Real.sinh_nonneg_iff.mpr hh
    have hs2 := (sq_le_sq₀ hh hs0).mpr hs
    have hc := Real.cosh_two_mul (p / 2)
    rw [show 2 * (p / 2) = p by ring] at hc
    nlinarith [Real.cosh_sq_sub_sinh_sq (p / 2)]
  have hlower (t : ℝ) : Real.exp t / 2 ≤ Real.cosh t := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-t)]
  have hupper : Real.cosh d - 1 ≤ Real.exp d / 2 := by
    have hn : Real.exp (-d) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr hd0)
    rw [Real.cosh_eq]
    linarith
  have hden : Real.exp (a + b) / 4 ≤ Real.cosh a * Real.cosh b := by
    rw [Real.exp_add]
    calc
      _ = (Real.exp a / 2) * (Real.exp b / 2) := by ring
      _ ≤ _ := mul_le_mul (hlower a) (hlower b) (by positivity) (Real.cosh_pos a).le
  have hc := cosh_dist_lineProjection_sub_one_le e he x y
  change Real.cosh p - 1 ≤ (Real.cosh d - 1) / (Real.cosh a * Real.cosh b) at hc
  have hprod : (p ^ 2 / 2) * (Real.exp (a + b) / 4) ≤ Real.exp d / 2 :=
    (mul_le_mul hp hden (by positivity) (sub_nonneg.mpr (Real.one_le_cosh p))).trans
      (((le_div_iff₀ (mul_pos (Real.cosh_pos a) (Real.cosh_pos b))).mp hc).trans hupper)
  have hp2 : p ^ 2 ≤ 4 * Real.exp (d - a - b) := by
    rw [show d - a - b = d - (a + b) by ring, Real.exp_sub, ← mul_div_assoc]
    apply (le_div_iff₀ (Real.exp_pos (a + b))).mpr
    nlinarith [hprod]
  have hexp : Real.exp ((d - a - b) / 2) ^ 2 = Real.exp (d - a - b) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ hp0 (by positivity)).mp
  calc
    p ^ 2 ≤ 4 * Real.exp (d - a - b) := hp2
    _ = (2 * Real.exp ((d - a - b) / 2)) ^ 2 := by rw [mul_pow, hexp]; norm_num

end DifferentialGeometry.Hyperboloid
