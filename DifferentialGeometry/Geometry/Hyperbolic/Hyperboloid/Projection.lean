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

end DifferentialGeometry.Hyperboloid
