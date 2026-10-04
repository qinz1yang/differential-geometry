import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphShape

/-!
# The spherical compact triangle: walls, reflections, compactness

Lane CF-S, tier 1, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §2, errata of review 23). For a spherical
`CompactShape` the plane is all of `ℂ` (`plane_sph`), and the three side functions are explicit:
`w₀ = Im z`, `w₁ = sin θ₃ Re z - cos θ₃ Im z` and the quadratic
`w₂ = sin θ₂ (t₂₃ (1 - ‖z‖²) - (1 - t₂₃²) Re z) - cos θ₂ (1 + t₂₃²) Im z`
(`wallSide_two_apply_sph`),
a positive multiple of `1 - ‖z‖² - 2 Re (z ā)` for the centre `-a` of the great circle of wall 2.

On the triangle `Re z ≥ 0`, `Im z ≥ 0`, hence `‖z‖ ≤ 1` (`norm_le_one_of_mem_sph`): the triangle
lies in
the closed hemisphere about `v₃`, and it is compact (`isCompact_triangle_sph`). The vertices lie on
their walls and in the triangle. The side functions are, up to explicit positive factors, the
imaginary parts of the rotated disc coordinates (`wallSide_zero_eq_rotTwo_sph`,
`wallSide_one_eq_rotOne_sph`, `wallSide_two_eq_rotOne_sph`), so on the triangle `rotTwo` and
`rotOne` lie
in their closed sectors `[0, θ₂]`, `[0, θ₁]` (`sector_two_sph`, `sector_one_sph`).

The reflections `refl 0 = conj`, `refl 1 = e^{2iθ₃} conj` are involutions fixing their walls and
reversing their side functions. The reflection in wall 2 is complex conjugation in the coordinate
`rotTwo` (`rotTwo_refl_two_sph`); on its chart domain `reflChart 2`, which it preserves, it is an
involution (`refl_refl_two_sph`), it reverses `w₂` up to a positive factor (`wallSide_refl_two_sph`)
and
it fixes wall 2 (`refl_two_eq_self_sph`). Each reflection preserves the chordal distance
`‖sphMoeb v ·‖` to the two vertices of its wall (`norm_sphMoeb_refl_*`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace GC.Seifert

namespace CompactShape

variable {σ : CompactShape}

theorem wallSide_zero_apply_sph (z : ℂ) : σ.wallSide 0 z = z.im := rfl

theorem wallSide_one_apply_sph (z : ℂ) :
    σ.wallSide 1 z = Real.sin σ.θ₃ * z.re - Real.cos σ.θ₃ * z.im := by
  change (exp ((σ.θ₃ : ℂ) * I) * conj z).im = _
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem sq_norm_eq_sph (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem wallSide_zero_zero_sph : σ.wallSide 0 0 = 0 := by
  simp [wallSide_zero_apply_sph]

theorem wallSide_one_zero_sph : σ.wallSide 1 0 = 0 := by
  simp [wallSide_one_apply_sph]

theorem wallSide_zero_vertexTwo_sph : σ.wallSide 0 σ.vertexTwo = 0 := by
  simp [wallSide_zero_apply_sph, vertexTwo_eq_sph]

theorem wallSide_one_vertexOne_sph : σ.wallSide 1 σ.vertexOne = 0 := by
  rw [wallSide_one_apply_sph, vertexOne_eq_sph]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
  ring


theorem im_exp_mul_conj_sph (θ : ℝ) (w : ℂ) :
    (exp ((θ : ℂ) * I) * conj w).im = Real.sin θ * w.re - Real.cos θ * w.im := by
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem re_nonneg_of_sector_sph {θ : ℝ} (h0 : 0 < θ) (hθ : θ ≤ Real.pi / 2) {w : ℂ}
    (h1 : 0 ≤ w.im) (h2 : 0 ≤ (exp ((θ : ℂ) * I) * conj w).im) : 0 ≤ w.re := by
  rw [im_exp_mul_conj_sph] at h2
  have hs := EuclidShape.sin_pos_aux h0 hθ
  have hc := EuclidShape.cos_nonneg_aux h0 hθ
  have := mul_nonneg hc h1
  by_contra h
  push Not at h
  nlinarith [mul_neg_of_pos_of_neg hs h]

theorem exp_two_mul_eq_sph (θ : ℝ) :
    exp (2 * (θ : ℂ) * I) = exp ((θ : ℂ) * I) * exp ((θ : ℂ) * I) := by
  rw [← Complex.exp_add]
  ring_nf

theorem refl_zero_apply_sph (z : ℂ) : σ.refl 0 z = conj z := rfl

theorem refl_one_apply_sph (z : ℂ) : σ.refl 1 z = exp (2 * (σ.θ₃ : ℂ) * I) * conj z := rfl

theorem refl_refl_zero_sph (z : ℂ) : σ.refl 0 (σ.refl 0 z) = z := Complex.conj_conj z

theorem refl_refl_one_sph (z : ℂ) : σ.refl 1 (σ.refl 1 z) = z := by
  rw [refl_one_apply_sph, refl_one_apply_sph, map_mul, Complex.conj_conj, exp_two_mul_eq_sph,
      map_mul,
    conj_exp_ofReal_mul_I_sph]
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination (exp ((σ.θ₃ : ℂ) * I) * exp (-((σ.θ₃ : ℂ) * I)) + 1) * z * this

theorem wallSide_refl_zero_sph (z : ℂ) : σ.wallSide 0 (σ.refl 0 z) = -σ.wallSide 0 z := by
  simp [wallSide_zero_apply_sph, refl_zero_apply_sph]

theorem wallSide_refl_one_sph (z : ℂ) : σ.wallSide 1 (σ.refl 1 z) = -σ.wallSide 1 z := by
  change (exp ((σ.θ₃ : ℂ) * I) * conj (σ.refl 1 z)).im = -(exp ((σ.θ₃ : ℂ) * I) * conj z).im
  have e : exp ((σ.θ₃ : ℂ) * I) * conj (σ.refl 1 z) =
      conj (exp ((σ.θ₃ : ℂ) * I) * conj z) := by
    rw [refl_one_apply_sph, map_mul, map_mul, Complex.conj_conj, exp_two_mul_eq_sph, map_mul,
      conj_exp_ofReal_mul_I_sph]
    have := exp_mul_exp_neg_sph σ.θ₃
    linear_combination (exp (-((σ.θ₃ : ℂ) * I)) * z) * this
  rw [e, Complex.conj_im]

theorem refl_zero_eq_self_sph {z : ℂ} (h : σ.wallSide 0 z = 0) : σ.refl 0 z = z :=
  Complex.conj_eq_iff_im.2 h

theorem refl_one_eq_self_sph {z : ℂ} (h : σ.wallSide 1 z = 0) : σ.refl 1 z = z := by
  have h' : conj (exp ((σ.θ₃ : ℂ) * I) * conj z) = exp ((σ.θ₃ : ℂ) * I) * conj z :=
    Complex.conj_eq_iff_im.2 h
  rw [map_mul, Complex.conj_conj, conj_exp_ofReal_mul_I_sph] at h'
  rw [refl_one_apply_sph, exp_two_mul_eq_sph, mul_assoc, ← h']
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination z * this

theorem norm_refl_zero_sph (z : ℂ) : ‖σ.refl 0 z‖ = ‖z‖ := Complex.norm_conj z

theorem norm_exp_mul_I_sph' (θ : ℝ) : ‖exp ((θ : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

theorem norm_refl_one_sph (z : ℂ) : ‖σ.refl 1 z‖ = ‖z‖ := by
  rw [refl_one_apply_sph, norm_mul, exp_two_mul_eq_sph, norm_mul, norm_exp_mul_I_sph',
      Complex.norm_conj]
  ring

theorem sphMoeb_vertexTwo_refl_zero (z : ℂ) :
    sphMoeb σ.vertexTwo (σ.refl 0 z) = conj (sphMoeb σ.vertexTwo z) := by
  rw [refl_zero_apply_sph, ← sphMoeb_conj, conj_vertexTwo_sph]

theorem conj_mul_exp_two_sph (θ : ℝ) :
    conj (exp (2 * (θ : ℂ) * I)) * exp (2 * (θ : ℂ) * I) = 1 := by
  rw [exp_two_mul_eq_sph, map_mul, conj_exp_ofReal_mul_I_sph]
  have := exp_mul_exp_neg_sph θ
  linear_combination (exp ((θ : ℂ) * I) * exp (-((θ : ℂ) * I)) + 1) * this

theorem vertexOne_eq_exp_two_mul_conj_sph :
    σ.vertexOne = exp (2 * (σ.θ₃ : ℂ) * I) * conj σ.vertexOne := by
  rw [conj_vertexOne_sph, vertexOne_eq_sph, exp_two_mul_eq_sph]
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination (-(σ.sphTOneThree : ℂ) * exp ((σ.θ₃ : ℂ) * I)) * this

theorem sphMoeb_vertexOne_refl_one (z : ℂ) :
    sphMoeb σ.vertexOne (σ.refl 1 z) =
      exp (2 * (σ.θ₃ : ℂ) * I) * conj (sphMoeb σ.vertexOne z) := by
  conv_lhs => rw [vertexOne_eq_exp_two_mul_conj_sph, refl_one_apply_sph]
  rw [sphMoeb_mul_unit (conj_mul_exp_two_sph σ.θ₃), sphMoeb_conj]

theorem norm_sphMoeb_vertexTwo_refl_zero (z : ℂ) :
    ‖sphMoeb σ.vertexTwo (σ.refl 0 z)‖ = ‖sphMoeb σ.vertexTwo z‖ := by
  rw [sphMoeb_vertexTwo_refl_zero, Complex.norm_conj]

theorem norm_sphMoeb_vertexOne_refl_one (z : ℂ) :
    ‖sphMoeb σ.vertexOne (σ.refl 1 z)‖ = ‖sphMoeb σ.vertexOne z‖ := by
  rw [sphMoeb_vertexOne_refl_one, norm_mul, exp_two_mul_eq_sph, norm_mul, norm_exp_mul_I_sph',
    Complex.norm_conj]
  ring

theorem norm_sphMoeb_le_one {a z : ℂ} (ha : ‖a‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (hre : 0 ≤ (conj a * z).re) : ‖sphMoeb a z‖ ≤ 1 := by
  have hd : 0 < (1 + conj a * z).re := by
    simp only [add_re, one_re]
    linarith
  have hne : 1 + conj a * z ≠ 0 := by
    intro h
    rw [h, zero_re] at hd
    exact lt_irrefl _ hd
  rw [sphMoeb, norm_div, div_le_one (norm_pos_iff.2 hne)]
  have key : ‖z - a‖ ^ 2 ≤ ‖1 + conj a * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    have h1 : (z - a).re = z.re - a.re := sub_re z a
    have h2 : (z - a).im = z.im - a.im := sub_im z a
    have h3 : (1 + conj a * z).re = 1 + (a.re * z.re + a.im * z.im) := by
      simp [mul_re]
    have h4 : (1 + conj a * z).im = a.re * z.im - a.im * z.re := by
      simp [mul_im]
      ring
    have h5 : (conj a * z).re = a.re * z.re + a.im * z.im := by
      simp [mul_re]
    rw [h1, h2, h3, h4]
    rw [h5] at hre
    have ha' : a.re ^ 2 + a.im ^ 2 ≤ 1 := by rw [← sq_norm_eq_sph]; nlinarith [norm_nonneg a]
    have hz' : z.re ^ 2 + z.im ^ 2 ≤ 1 := by rw [← sq_norm_eq_sph]; nlinarith [norm_nonneg z]
    nlinarith [mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hz')]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 key

theorem conj_vertexOne_mul_re_sph (z : ℂ) : (conj σ.vertexOne * z).re =
    σ.sphTOneThree * (Real.cos σ.θ₃ * z.re + Real.sin σ.θ₃ * z.im) := by
  rw [conj_vertexOne_sph, exp_neg_ofReal_mul_I_sph]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg, zero_mul, sub_zero]
  ring

theorem one_add_ne_of_re_nonneg_sph {w : ℂ} (h : 0 ≤ w.re) : 1 + w ≠ 0 := by
  intro h'
  have := congrArg Complex.re h'
  simp only [add_re, one_re, zero_re] at this
  linarith

theorem im_sphMoeb_real (s : ℝ) (w : ℂ) : (sphMoeb s w).im * Complex.normSq (1 + s * w) =
    (1 + s ^ 2) * w.im := by
  rw [sphMoeb, Complex.conj_ofReal]
  by_cases h0 : 1 + (s : ℂ) * w = 0
  · rw [h0]
    have hw : w.im = 0 := by
      have := congrArg Complex.im h0
      simp only [add_im, one_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
        zero_im, zero_add] at this
      rcases mul_eq_zero.1 this with h | h
      · rw [h] at h0
        simp at h0
      · exact h
    simp [hw]
  · have hN : Complex.normSq (1 + (s : ℂ) * w) ≠ 0 := (Complex.normSq_pos.2 h0).ne'
    rw [Complex.div_im, sub_mul, div_mul_cancel₀ _ hN, div_mul_cancel₀ _ hN]
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, one_re,
      one_im]
    ring


theorem exp_neg_two_mul_eq_sph (θ : ℝ) :
    exp (-(2 * (θ : ℂ) * I)) = exp (-((θ : ℂ) * I)) * exp (-((θ : ℂ) * I)) := by
  rw [← Complex.exp_add]
  ring_nf

theorem conj_exp_neg_sph (θ : ℝ) : conj (exp (-((θ : ℂ) * I))) = exp ((θ : ℂ) * I) := by
  rw [← conj_exp_ofReal_mul_I_sph, Complex.conj_conj]

theorem conj_exp_neg_two_mul_sph (θ : ℝ) :
    conj (exp (-(2 * (θ : ℂ) * I))) * exp (-(2 * (θ : ℂ) * I)) = 1 := by
  rw [exp_neg_two_mul_eq_sph, map_mul, conj_exp_neg_sph]
  have := exp_mul_exp_neg_sph θ
  linear_combination (exp ((θ : ℂ) * I) * exp (-((θ : ℂ) * I)) + 1) * this

theorem norm_exp_neg_two_mul_sph (θ : ℝ) : ‖exp (-(2 * (θ : ℂ) * I))‖ = 1 :=
  norm_eq_one_of_conj_mul_sph (conj_exp_neg_two_mul_sph θ)

theorem one_add_vertexTwo_mul_self_ne_sph : 1 + σ.vertexTwo * σ.vertexTwo ≠ 0 := by
  have := one_add_conj_mul_self_ne_sph σ.vertexTwo
  rwa [conj_vertexTwo_sph] at this

theorem one_sub_vertexTwo_mul_sphMoeb_ne {z : ℂ} (h1 : 1 + σ.vertexTwo * z ≠ 0) :
    1 - σ.vertexTwo * sphMoeb σ.vertexTwo z ≠ 0 := by
  have e := one_sub_conj_mul_sphMoeb (a := σ.vertexTwo) (z := z)
    (by rw [conj_vertexTwo_sph]; exact h1)
  rw [conj_vertexTwo_sph] at e
  rw [e]
  exact div_ne_zero one_add_vertexTwo_mul_self_ne_sph h1

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem plane_sph : σ.plane = univ := by
  ext z
  simp only [plane, eps_sph hs, mem_ofPred_eq, mem_univ, iff_true]
  have := norm_nonneg z
  nlinarith

theorem wallSide_two_apply_sph (z : ℂ) : σ.wallSide 2 z =
    Real.sin σ.θ₂ * (σ.sphTTwoThree * (1 - ‖z‖ ^ 2) - (1 - σ.sphTTwoThree ^ 2) * z.re) -
      Real.cos σ.θ₂ * (1 + σ.sphTTwoThree ^ 2) * z.im := by
  change (-(exp ((σ.θ₂ : ℂ) * I) * ((z - σ.vertexTwo) *
    conj (1 - σ.eps * conj σ.vertexTwo * z)))).im = _
  rw [eps_sph hs, conj_vertexTwo_sph, vertexTwo_eq_sph, sq_norm_eq_sph]
  simp only [neg_im, mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, conj_re, conj_im,
    one_re, one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, neg_re,
    ofReal_neg, ofReal_one]
  ring

theorem mem_triangle_iff_sph {z : ℂ} : z ∈ σ.triangle ↔
    0 ≤ σ.wallSide 0 z ∧ 0 ≤ σ.wallSide 1 z ∧ 0 ≤ σ.wallSide 2 z := by
  rw [triangle, plane_sph hs]
  simp only [mem_ofPred_eq, mem_univ, true_and, Fin.forall_fin_succ, IsEmpty.forall_iff,
    and_true]
  rfl

theorem im_nonneg_of_mem_sph {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ z.im :=
  ((mem_triangle_iff_sph hs).1 hz).1

theorem re_nonneg_of_mem_sph {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ z.re := by
  have h1 := ((mem_triangle_iff_sph hs).1 hz).2.1
  rw [wallSide_one_apply_sph] at h1
  have := im_nonneg_of_mem_sph hs hz
  have := mul_nonneg σ.cos_θ₃_nonneg_sph this
  have hs3 := σ.sin_θ₃_pos_sph
  by_contra h
  push Not at h
  nlinarith [mul_neg_of_pos_of_neg hs3 h]

theorem norm_le_one_of_mem_sph {z : ℂ} (hz : z ∈ σ.triangle) : ‖z‖ ≤ 1 := by
  have h2 := ((mem_triangle_iff_sph hs).1 hz).2.2
  rw [wallSide_two_apply_sph hs] at h2
  have hx := re_nonneg_of_mem_sph hs hz
  have hy := im_nonneg_of_mem_sph hs hz
  have ht := tTwoThree_pos_sph hs
  have ht1 := tTwoThree_le_one_sph hs
  have hs2 := σ.sin_θ₂_pos_sph
  have hc2 := σ.cos_θ₂_nonneg_sph
  have e1 : 0 ≤ Real.sin σ.θ₂ * ((1 - σ.sphTTwoThree ^ 2) * z.re) :=
    mul_nonneg hs2.le (mul_nonneg (by nlinarith) hx)
  have e2 : 0 ≤ Real.cos σ.θ₂ * (1 + σ.sphTTwoThree ^ 2) * z.im :=
    mul_nonneg (mul_nonneg hc2 (by positivity)) hy
  have e3 : 0 ≤ Real.sin σ.θ₂ * σ.sphTTwoThree * (1 - ‖z‖ ^ 2) := by nlinarith
  have e4 : 0 ≤ 1 - ‖z‖ ^ 2 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hs2 ht]
  have := norm_nonneg z
  nlinarith

theorem continuous_wallSide_sph (i : Fin 3) : Continuous (σ.wallSide i) := by
  fin_cases i
  · exact Complex.continuous_im
  · change Continuous (σ.wallSide 1)
    simp only [funext wallSide_one_apply_sph]
    fun_prop
  · change Continuous (σ.wallSide 2)
    simp only [funext (wallSide_two_apply_sph hs)]
    fun_prop

theorem isClosed_triangle_sph : IsClosed σ.triangle := by
  have e : σ.triangle = ⋂ i, σ.wallSide i ⁻¹' Ici 0 := by
    ext z
    simp only [triangle, plane_sph hs, mem_ofPred_eq, mem_univ, true_and, mem_iInter,
      mem_preimage, mem_Ici]
  rw [e]
  exact isClosed_iInter fun i => isClosed_Ici.preimage (continuous_wallSide_sph hs i)

theorem isCompact_triangle_sph : IsCompact σ.triangle := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_triangle_sph hs) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_one_of_mem_sph hs hz

theorem wallSide_two_eq_sph (z : ℂ) :
    σ.wallSide 2 z = (σ.rotTwo z).im * Complex.normSq (1 + σ.vertexTwo * z) := by
  rw [wallSide_two_eq, eps_sph hs, conj_vertexTwo_sph]
  congr 2
  push_cast
  ring

theorem wallSide_two_vertexTwo_sph : σ.wallSide 2 σ.vertexTwo = 0 := by
  rw [wallSide_two_eq_sph hs, rotTwo_vertexTwo_sph hs]
  simp

theorem wallSide_two_vertexOne_sph : σ.wallSide 2 σ.vertexOne = 0 := by
  rw [wallSide_two_eq_sph hs, rotTwo_vertexOne_sph hs]
  simp

theorem wallSide_zero_vertexOne_pos_sph : 0 < σ.wallSide 0 σ.vertexOne := by
  rw [wallSide_zero_apply_sph, vertexOne_eq_sph]
  simp only [mul_im, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  exact mul_pos (tOneThree_pos_sph hs) σ.sin_θ₃_pos_sph

theorem wallSide_one_vertexTwo_pos_sph : 0 < σ.wallSide 1 σ.vertexTwo := by
  rw [wallSide_one_apply_sph, vertexTwo_eq_sph]
  simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact mul_pos σ.sin_θ₃_pos_sph (tTwoThree_pos_sph hs)

theorem wallSide_two_zero_pos_sph : 0 < σ.wallSide 2 0 := by
  rw [wallSide_two_apply_sph hs]
  simp only [norm_zero, zero_re, zero_im, mul_zero, sub_zero]
  norm_num
  exact mul_pos σ.sin_θ₂_pos_sph (tTwoThree_pos_sph hs)

theorem zero_mem_triangle_sph : (0 : ℂ) ∈ σ.triangle :=
  (mem_triangle_iff_sph hs).2 ⟨wallSide_zero_zero_sph.ge, wallSide_one_zero_sph.ge,
    (wallSide_two_zero_pos_sph hs).le⟩

theorem vertexOne_mem_triangle_sph : σ.vertexOne ∈ σ.triangle :=
  (mem_triangle_iff_sph hs).2 ⟨(wallSide_zero_vertexOne_pos_sph hs).le,
      wallSide_one_vertexOne_sph.ge,
    (wallSide_two_vertexOne_sph hs).ge⟩

theorem vertexTwo_mem_triangle_sph : σ.vertexTwo ∈ σ.triangle :=
  (mem_triangle_iff_sph hs).2 ⟨wallSide_zero_vertexTwo_sph.ge, (wallSide_one_vertexTwo_pos_sph
      hs).le,
    (wallSide_two_vertexTwo_sph hs).ge⟩


theorem conj_vertexOne_mul_re_nonneg_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (conj σ.vertexOne * z).re := by
  rw [conj_vertexOne_mul_re_sph]
  have := re_nonneg_of_mem_sph hs hz
  have := im_nonneg_of_mem_sph hs hz
  have := tOneThree_pos_sph hs
  have := σ.cos_θ₃_nonneg_sph
  have := σ.sin_θ₃_pos_sph
  positivity

theorem vertexTwo_mul_re_nonneg_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (conj σ.vertexTwo * z).re := by
  rw [conj_vertexTwo_sph, vertexTwo_eq_sph]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (tTwoThree_pos_sph hs).le (re_nonneg_of_mem_sph hs hz)

theorem one_add_conj_vertexOne_ne_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    1 + conj σ.vertexOne * z ≠ 0 :=
  one_add_ne_of_re_nonneg_sph (conj_vertexOne_mul_re_nonneg_sph hs hz)

theorem one_add_vertexTwo_ne_sph {z : ℂ} (hz : z ∈ σ.triangle) : 1 + σ.vertexTwo * z ≠ 0 := by
  have := vertexTwo_mul_re_nonneg_sph hs hz
  rw [conj_vertexTwo_sph] at this
  exact one_add_ne_of_re_nonneg_sph this

theorem norm_vertexOne_sph : ‖σ.vertexOne‖ = σ.sphTOneThree := by
  rw [vertexOne_eq_sph, norm_mul, norm_exp_mul_I_sph', mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (tOneThree_pos_sph hs)]

theorem norm_vertexTwo_sph : ‖σ.vertexTwo‖ = σ.sphTTwoThree := by
  rw [vertexTwo_eq_sph, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (tTwoThree_pos_sph hs)]

theorem norm_rotTwo_sph (z : ℂ) : ‖σ.rotTwo z‖ = ‖sphMoeb σ.vertexTwo z‖ := by
  rw [rotTwo_eq_mul_sph hs, norm_mul, norm_neg, norm_exp_mul_I_sph', one_mul]

theorem norm_rotOne_sph (z : ℂ) : ‖σ.rotOne z‖ = ‖sphMoeb σ.vertexOne z‖ := by
  rw [rotOne_eq_mul_sph hs, norm_mul, norm_neg, exp_neg_ofReal_mul_I_sph, norm_exp_mul_I_sph',
      one_mul]

theorem norm_rotTwo_le_one_sph {z : ℂ} (hz : z ∈ σ.triangle) : ‖σ.rotTwo z‖ ≤ 1 := by
  rw [norm_rotTwo_sph hs]
  exact norm_sphMoeb_le_one ((norm_vertexTwo_sph hs).trans_le (tTwoThree_le_one_sph hs))
    (norm_le_one_of_mem_sph hs hz) (vertexTwo_mul_re_nonneg_sph hs hz)

theorem norm_rotOne_le_one_sph {z : ℂ} (hz : z ∈ σ.triangle) : ‖σ.rotOne z‖ ≤ 1 := by
  rw [norm_rotOne_sph hs]
  exact norm_sphMoeb_le_one ((norm_vertexOne_sph hs).trans_le (tOneThree_le_one_sph hs))
    (norm_le_one_of_mem_sph hs hz) (conj_vertexOne_mul_re_nonneg_sph hs hz)

theorem wallSide_zero_eq_rotTwo_sph (z : ℂ) : σ.wallSide 0 z * (1 + σ.sphTTwoThree ^ 2) =
    (exp ((σ.θ₂ : ℂ) * I) * conj (σ.rotTwo z)).im * Complex.normSq (1 + σ.vertexTwo * z) := by
  have e : exp ((σ.θ₂ : ℂ) * I) * conj (σ.rotTwo z) = -conj (sphMoeb σ.sphTTwoThree z) := by
    rw [rotTwo_eq_mul_sph hs, vertexTwo_eq_sph, map_mul, map_neg, conj_exp_ofReal_mul_I_sph]
    have := exp_mul_exp_neg_sph σ.θ₂
    linear_combination (-conj (sphMoeb (σ.sphTTwoThree : ℂ) z)) * this
  rw [e, neg_im, Complex.conj_im, neg_neg, vertexTwo_eq_sph, im_sphMoeb_real,
      wallSide_zero_apply_sph]
  ring

theorem wallSide_one_eq_rotOne_sph (z : ℂ) : σ.wallSide 1 z * (1 + σ.sphTOneThree ^ 2) =
    (σ.rotOne z).im * Complex.normSq (1 + conj σ.vertexOne * z) := by
  set w := exp (-((σ.θ₃ : ℂ) * I)) * z with hw
  have hu : conj (exp ((σ.θ₃ : ℂ) * I)) * exp ((σ.θ₃ : ℂ) * I) = 1 := conj_exp_mul_exp_sph σ.θ₃
  have hz : z = exp ((σ.θ₃ : ℂ) * I) * w := by
    rw [hw, ← mul_assoc, exp_mul_exp_neg_sph, one_mul]
  have e1 : σ.rotOne z = -sphMoeb σ.sphTOneThree w := by
    rw [rotOne_eq_mul_sph hs, vertexOne_eq_sph]
    conv_lhs => rw [hz, mul_comm (σ.sphTOneThree : ℂ), sphMoeb_mul_unit hu]
    have := exp_mul_exp_neg_sph σ.θ₃
    linear_combination (-sphMoeb (σ.sphTOneThree : ℂ) w) * this
  have e2 : conj σ.vertexOne * z = σ.sphTOneThree * w := by
    rw [conj_vertexOne_sph, hw]
    ring
  have e3 : σ.wallSide 1 z = -w.im := by
    change (exp ((σ.θ₃ : ℂ) * I) * conj z).im = -w.im
    have : exp ((σ.θ₃ : ℂ) * I) * conj z = conj w := by
      rw [hw, map_mul, ← conj_exp_ofReal_mul_I_sph, Complex.conj_conj]
    rw [this, Complex.conj_im]
  rw [e1, e2, e3, neg_im]
  linear_combination im_sphMoeb_real σ.sphTOneThree w

theorem wallSide_two_eq_rotOne_sph {z : ℂ} (h1 : 1 + conj σ.vertexOne * z ≠ 0)
    (h2 : 1 + conj σ.vertexTwo * z ≠ 0) :
    (exp ((σ.θ₁ : ℂ) * I) * conj (σ.rotOne z)).im *
      Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z) = (1 + σ.sphTOneTwo ^ 2) * (σ.rotTwo z).im :=
          by
  rw [rotOne_eq_rotTwo_sph hs h1 h2, ← im_sphMoeb_real]
  congr 1
  rw [map_neg, map_mul, conj_exp_ofReal_mul_I_sph, mul_neg, ← mul_assoc, exp_mul_exp_neg_sph,
      one_mul,
    neg_im, Complex.conj_im, neg_neg]

theorem sector_two_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.rotTwo z).im ∧ 0 ≤ (exp ((σ.θ₂ : ℂ) * I) * conj (σ.rotTwo z)).im := by
  have hN := Complex.normSq_pos.2 (one_add_vertexTwo_ne_sph hs hz)
  obtain ⟨h0, -, h2⟩ := (mem_triangle_iff_sph hs).1 hz
  constructor
  · rw [wallSide_two_eq_sph hs] at h2
    exact nonneg_of_mul_nonneg_left h2 hN
  · have e := wallSide_zero_eq_rotTwo_sph hs z
    have : 0 ≤ σ.wallSide 0 z * (1 + σ.sphTTwoThree ^ 2) := mul_nonneg h0 (by positivity)
    rw [e] at this
    exact nonneg_of_mul_nonneg_left this hN

theorem re_rotTwo_nonneg_sph {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ (σ.rotTwo z).re :=
  re_nonneg_of_sector_sph σ.θ₂_pos_sph σ.θ₂_le_sph (sector_two_sph hs hz).1 (sector_two_sph hs hz).2

theorem sector_one_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.rotOne z).im ∧ 0 ≤ (exp ((σ.θ₁ : ℂ) * I) * conj (σ.rotOne z)).im := by
  have h1 := one_add_conj_vertexOne_ne_sph hs hz
  have h2 : 1 + conj σ.vertexTwo * z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_ne_sph hs hz
  obtain ⟨-, hw1, -⟩ := (mem_triangle_iff_sph hs).1 hz
  constructor
  · have e := wallSide_one_eq_rotOne_sph hs z
    have : 0 ≤ σ.wallSide 1 z * (1 + σ.sphTOneThree ^ 2) := mul_nonneg hw1 (by positivity)
    rw [e] at this
    exact nonneg_of_mul_nonneg_left this (Complex.normSq_pos.2 h1)
  · have e := wallSide_two_eq_rotOne_sph hs h1 h2
    have hre := re_rotTwo_nonneg_sph hs hz
    have hN : 0 < Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z) := by
      refine Complex.normSq_pos.2 (one_add_ne_of_re_nonneg_sph ?_)
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (tOneTwo_pos_sph hs).le hre
    have : 0 ≤ (1 + σ.sphTOneTwo ^ 2) * (σ.rotTwo z).im :=
      mul_nonneg (by positivity) (sector_two_sph hs hz).1
    rw [← e] at this
    exact nonneg_of_mul_nonneg_left this hN

theorem re_rotOne_nonneg_sph {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ (σ.rotOne z).re :=
  re_nonneg_of_sector_sph σ.θ₁_pos_sph σ.θ₁_le_sph (sector_one_sph hs hz).1 (sector_one_sph hs hz).2


theorem reflTwoAux_sph (z : ℂ) :
    σ.reflTwoAux z = exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (sphMoeb σ.vertexTwo z) := by
  rw [reflTwoAux, disc_sph hs]

theorem refl_two_sph (z : ℂ) : σ.refl 2 z = sphMoebInv σ.vertexTwo (σ.reflTwoAux z) := by
  change σ.discInv σ.vertexTwo (σ.reflTwoAux z) = _
  rw [discInv_sph hs]

theorem mem_reflChart_two_iff_sph {z : ℂ} : z ∈ σ.reflChart 2 ↔
    1 + σ.vertexTwo * z ≠ 0 ∧ 1 - σ.vertexTwo * σ.reflTwoAux z ≠ 0 := by
  change (1 - σ.eps * conj σ.vertexTwo * z ≠ 0 ∧
    1 + σ.eps * conj σ.vertexTwo * σ.reflTwoAux z ≠ 0) ↔ _
  have e1 : (1 : ℂ) - ((-1 : ℝ) : ℂ) * σ.vertexTwo * z = 1 + σ.vertexTwo * z := by
    push_cast
    ring
  have e2 : (1 : ℂ) + ((-1 : ℝ) : ℂ) * σ.vertexTwo * σ.reflTwoAux z =
      1 - σ.vertexTwo * σ.reflTwoAux z := by
    push_cast
    ring
  rw [eps_sph hs, conj_vertexTwo_sph, e1, e2]

theorem sphMoeb_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    sphMoeb σ.vertexTwo (σ.refl 2 z) = σ.reflTwoAux z := by
  rw [refl_two_sph hs]
  apply sphMoeb_sphMoebInv
  rw [conj_vertexTwo_sph]
  exact ((mem_reflChart_two_iff_sph hs).1 hz).2

theorem rotTwo_refl_two_sph {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    σ.rotTwo (σ.refl 2 z) = conj (σ.rotTwo z) := by
  rw [rotTwo_eq_mul_sph hs, sphMoeb_refl_two hs hz, reflTwoAux_sph hs, rotTwo_eq_mul_sph hs,
      map_mul,
    map_neg, conj_exp_ofReal_mul_I_sph, exp_neg_two_mul_eq_sph]
  have := exp_mul_exp_neg_sph σ.θ₂
  linear_combination (-(exp (-((σ.θ₂ : ℂ) * I)) * conj (sphMoeb σ.vertexTwo z))) * this

theorem one_add_vertexTwo_mul_refl_two_sph {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    1 + σ.vertexTwo * σ.refl 2 z ≠ 0 := by
  have h2 := ((mem_reflChart_two_iff_sph hs).1 hz).2
  have e := one_add_conj_mul_sphMoebInv (a := σ.vertexTwo) (w := σ.reflTwoAux z)
    (by rw [conj_vertexTwo_sph]; exact h2)
  rw [conj_vertexTwo_sph, ← refl_two_sph hs] at e
  rw [e]
  exact div_ne_zero one_add_vertexTwo_mul_self_ne_sph h2

theorem reflTwoAux_refl_two_sph {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    σ.reflTwoAux (σ.refl 2 z) = sphMoeb σ.vertexTwo z := by
  rw [reflTwoAux_sph hs, sphMoeb_refl_two hs hz, reflTwoAux_sph hs, map_mul,
    Complex.conj_conj, ← mul_assoc, mul_comm (exp _), conj_exp_neg_two_mul_sph, one_mul]

theorem refl_two_mem_reflChart_sph {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    σ.refl 2 z ∈ σ.reflChart 2 := by
  refine (mem_reflChart_two_iff_sph hs).2 ⟨one_add_vertexTwo_mul_refl_two_sph hs hz, ?_⟩
  rw [reflTwoAux_refl_two_sph hs hz]
  exact one_sub_vertexTwo_mul_sphMoeb_ne ((mem_reflChart_two_iff_sph hs).1 hz).1

theorem refl_refl_two_sph {z : ℂ} (hz : z ∈ σ.reflChart 2) : σ.refl 2 (σ.refl 2 z) = z := by
  rw [refl_two_sph hs (σ.refl 2 z), reflTwoAux_refl_two_sph hs hz]
  exact sphMoebInv_sphMoeb (by rw [conj_vertexTwo_sph]; exact ((mem_reflChart_two_iff_sph hs).1
      hz).1)

theorem wallSide_refl_two_sph {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    σ.wallSide 2 (σ.refl 2 z) * Complex.normSq (1 + σ.vertexTwo * z) =
      -(σ.wallSide 2 z * Complex.normSq (1 + σ.vertexTwo * σ.refl 2 z)) := by
  rw [wallSide_two_eq_sph hs, wallSide_two_eq_sph hs, rotTwo_refl_two_sph hs hz, Complex.conj_im]
  ring

theorem wallSide_refl_two_sph' {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    σ.wallSide 2 (σ.refl 2 z) = -(Complex.normSq (1 + σ.vertexTwo * σ.refl 2 z) /
      Complex.normSq (1 + σ.vertexTwo * z)) * σ.wallSide 2 z := by
  have hN := (Complex.normSq_pos.2 ((mem_reflChart_two_iff_sph hs).1 hz).1).ne'
  have key := wallSide_refl_two_sph hs hz
  field_simp
  linear_combination key

theorem reflTwoAux_eq_of_wall_sph {z : ℂ} (hw : σ.wallSide 2 z = 0)
    (h1 : 1 + σ.vertexTwo * z ≠ 0) : σ.reflTwoAux z = sphMoeb σ.vertexTwo z := by
  have him : (σ.rotTwo z).im = 0 := by
    rw [wallSide_two_eq_sph hs] at hw
    exact (mul_eq_zero.1 hw).resolve_right (Complex.normSq_pos.2 h1).ne'
  have hc : conj (σ.rotTwo z) = σ.rotTwo z := Complex.conj_eq_iff_im.2 him
  rw [rotTwo_eq_mul_sph hs, map_mul, map_neg, conj_exp_ofReal_mul_I_sph] at hc
  rw [reflTwoAux_sph hs, exp_neg_two_mul_eq_sph]
  have := exp_mul_exp_neg_sph σ.θ₂
  linear_combination (-exp (-((σ.θ₂ : ℂ) * I))) * hc + sphMoeb σ.vertexTwo z * this

theorem mem_reflChart_two_of_wall_sph {z : ℂ} (hw : σ.wallSide 2 z = 0)
    (h1 : 1 + σ.vertexTwo * z ≠ 0) : z ∈ σ.reflChart 2 := by
  refine (mem_reflChart_two_iff_sph hs).2 ⟨h1, ?_⟩
  rw [reflTwoAux_eq_of_wall_sph hs hw h1]
  exact one_sub_vertexTwo_mul_sphMoeb_ne h1

theorem refl_two_eq_self_sph {z : ℂ} (hw : σ.wallSide 2 z = 0) (h1 : 1 + σ.vertexTwo * z ≠ 0) :
    σ.refl 2 z = z := by
  rw [refl_two_sph hs, reflTwoAux_eq_of_wall_sph hs hw h1]
  exact sphMoebInv_sphMoeb (by rw [conj_vertexTwo_sph]; exact h1)

theorem norm_sphMoeb_vertexTwo_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    ‖sphMoeb σ.vertexTwo (σ.refl 2 z)‖ = ‖sphMoeb σ.vertexTwo z‖ := by
  rw [sphMoeb_refl_two hs hz, reflTwoAux_sph hs, norm_mul, Complex.norm_conj,
    norm_exp_neg_two_mul_sph, one_mul]

theorem sphMoeb_vertexTwo_vertexOne :
    sphMoeb σ.vertexTwo σ.vertexOne = -(exp (-((σ.θ₂ : ℂ) * I)) * σ.sphTOneTwo) := by
  have h := rotTwo_vertexOne_sph hs
  rw [rotTwo_eq_mul_sph hs] at h
  have := exp_mul_exp_neg_sph σ.θ₂
  linear_combination (-exp (-((σ.θ₂ : ℂ) * I))) * h - sphMoeb σ.vertexTwo σ.vertexOne * this

theorem norm_sphMoeb_vertexOne_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (h1 : 1 + conj σ.vertexOne * z ≠ 0) :
    ‖sphMoeb σ.vertexOne (σ.refl 2 z)‖ = ‖sphMoeb σ.vertexOne z‖ := by
  set a := sphMoeb σ.vertexTwo σ.vertexOne with ha_def
  set u := exp (-(2 * (σ.θ₂ : ℂ) * I)) with hu_def
  have hu : conj u * u = 1 := conj_exp_neg_two_mul_sph σ.θ₂
  have hv : 1 + conj σ.vertexTwo * σ.vertexOne ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_mul_vertexOne_ne_sph hs
  have hz1 : 1 + conj σ.vertexTwo * z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact ((mem_reflChart_two_iff_sph hs).1 hz).1
  have hr1 : 1 + conj σ.vertexTwo * σ.refl 2 z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_mul_refl_two_sph hs hz
  have ha : a = u * conj a := by
    rw [ha_def, sphMoeb_vertexTwo_vertexOne hs, hu_def, map_neg, map_mul,
      Complex.conj_ofReal, conj_exp_neg_sph, exp_neg_two_mul_eq_sph]
    have := exp_mul_exp_neg_sph σ.θ₂
    linear_combination (exp (-((σ.θ₂ : ℂ) * I)) * σ.sphTOneTwo) * this
  have hω : sphMoeb σ.vertexTwo (σ.refl 2 z) = u * conj (sphMoeb σ.vertexTwo z) := by
    rw [sphMoeb_refl_two hs hz, reflTwoAux_sph hs]
  have hca : conj a * u = a := by
    conv_rhs => rw [ha]
    ring
  have hA : ∀ w, 1 + conj σ.vertexTwo * w ≠ 0 →
      (1 + conj a * sphMoeb σ.vertexTwo w = 0 ↔ 1 + conj σ.vertexOne * w = 0) := by
    intro w hw
    rw [ha_def, one_add_conj_sphMoeb_mul hw hv]
    have hvv := one_add_conj_mul_self_ne_sph σ.vertexTwo
    have hv' := one_add_mul_conj_ne_sph hv
    constructor
    · intro h
      rcases div_eq_zero_iff.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hvv
        · exact h
      · exact absurd h (mul_ne_zero hv' hw)
    · intro h
      simp [h]
  have h1' : 1 + conj σ.vertexOne * σ.refl 2 z ≠ 0 := by
    intro h
    have h' := (hA _ hr1).2 h
    rw [hω, ← mul_assoc, hca] at h'
    have h'' : 1 + conj a * sphMoeb σ.vertexTwo z = 0 := by
      have := congrArg conj h'
      rw [map_add, map_one, map_mul, Complex.conj_conj, map_zero] at this
      exact this
    exact h1 ((hA z hz1).1 h'')
  rw [← norm_sphMoeb_comp hr1 hv h1', ← norm_sphMoeb_comp hz1 hv h1, hω, ← ha_def]
  conv_lhs => rw [ha]
  rw [norm_sphMoeb_mul_unit hu, sphMoeb_conj, Complex.norm_conj]

end Spherical

end CompactShape

end GC.Seifert
