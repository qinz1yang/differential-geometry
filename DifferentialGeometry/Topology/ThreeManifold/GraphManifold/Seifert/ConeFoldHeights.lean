import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldAngles

/-!
# Derivatives of the virtual heights along the level curves of the corners

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5).
The angle of a bridge about the centre of a corner moves at the speed of the other virtual height
divided by the wall function (`ConeFoldAngles`). These are the explicit quotients:

* along horizontal lines (the horocycles of the cusp `∞`), the virtual height of a point `v` of the
  upper half-plane has derivative `Im ω · (-4 y Im v / ((1 - |ω|)² |ω| |z - v̄|²))`, `ω` its disc
  coordinate (`hasDerivAt_coneHeight_horizontal`): it decreases towards the vertical line through
  `v`, the factor `Im ω` being that line's side function;
* along horizontal lines, the cusp-`0` virtual height `|z|²/y` has derivative `2x/y`
  (`hasDerivAt_cuspZeroHeight_horizontal`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem norm_coneDisc_eq_sqrt (v z : ℂ) :
    ‖coneDisc v z‖ = Real.sqrt (normSq (z - v) / normSq (z - conj v)) := by
  rw [← normSq_coneDisc, ← Complex.sq_norm, Real.sqrt_sq (norm_nonneg _)]

theorem hasDerivAt_coneHeight_horizontal {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im)
    (hzv : z ≠ v) :
    HasDerivAt (fun t : ℝ => coneHeight v (z + t))
      ((coneDisc v z).im * (-(4 * z.im * v.im) /
        ((1 - ‖coneDisc v z‖) ^ 2 * ‖coneDisc v z‖ * normSq (z - conj v)))) 0 := by
  set x := z.re
  set y := z.im
  let N : ℝ → ℝ := fun t => (x + t - v.re) ^ 2 + (y - v.im) ^ 2
  let D : ℝ → ℝ := fun t => (x + t - v.re) ^ 2 + (y + v.im) ^ 2
  have hN : ∀ t : ℝ, normSq (z + t - v) = N t := fun t => by
    simp only [N, normSq_apply, sub_re, add_re, ofReal_re, sub_im, add_im, ofReal_im, add_zero, x,
      y]
    ring
  have hD : ∀ t : ℝ, normSq (z + t - conj v) = D t := fun t => by
    simp only [D, normSq_apply, sub_re, add_re, ofReal_re, conj_re, sub_im, add_im, ofReal_im,
      conj_im, add_zero, x, y]
    ring
  have hDpos : ∀ t, 0 < D t := fun t => by
    simp only [D]
    have : 0 < y + v.im := by linarith
    positivity
  have hN0 : 0 < N 0 := by
    have h := normSq_pos.2 (sub_ne_zero.2 hzv)
    rw [← hN 0]
    simpa using h
  set r := ‖coneDisc v z‖ with hr
  have hrt : ∀ t : ℝ, ‖coneDisc v (z + t)‖ = Real.sqrt (N t / D t) := fun t => by
    rw [norm_coneDisc_eq_sqrt, hN, hD]
  have hr0 : r = Real.sqrt (N 0 / D 0) := by rw [hr, ← hrt 0]; simp
  have hrpos : 0 < r := by rw [hr0]; exact Real.sqrt_pos.2 (div_pos hN0 (hDpos 0))
  have hr1 : r < 1 := norm_coneDisc_lt_one hv hz
  have hND : HasDerivAt (fun t => N t / D t)
      (2 * (x - v.re) * (4 * y * v.im) / D 0 ^ 2) 0 := by
    have h1 : HasDerivAt N (2 * (x - v.re)) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).const_add x |>.sub_const v.re).pow 2 |>.add_const
        ((y - v.im) ^ 2)
      convert this using 1
      simp
    have h2 : HasDerivAt D (2 * (x - v.re)) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).const_add x |>.sub_const v.re).pow 2 |>.add_const
        ((y + v.im) ^ 2)
      convert this using 1
      simp
    have := h1.div h2 (hDpos 0).ne'
    refine this.congr_deriv ?_
    simp only [N, D, add_zero]
    field_simp
    ring
  have hsq : HasDerivAt (fun t => Real.sqrt (N t / D t))
      (2 * (x - v.re) * (4 * y * v.im) / D 0 ^ 2 / (2 * r)) 0 := by
    have := hND.sqrt (div_pos hN0 (hDpos 0)).ne'
    rw [← hr0] at this
    exact this
  have hη : HasDerivAt (fun t : ℝ => v.im * (1 + Real.sqrt (N t / D t)) /
      (1 - Real.sqrt (N t / D t)))
      (v.im * 2 / (1 - r) ^ 2 * (2 * (x - v.re) * (4 * y * v.im) / D 0 ^ 2 / (2 * r))) 0 := by
    have h1 := (hsq.const_add 1).const_mul v.im
    have h2 := hsq.const_sub 1
    have h1r : 1 - Real.sqrt (N 0 / D 0) ≠ 0 := by rw [← hr0]; linarith
    have := h1.div h2 h1r
    refine this.congr_deriv ?_
    rw [← hr0]
    field_simp
    ring
  have heq : (fun t : ℝ => coneHeight v (z + t)) =
      fun t : ℝ => v.im * (1 + Real.sqrt (N t / D t)) / (1 - Real.sqrt (N t / D t)) := by
    funext t
    rw [coneHeight, hrt]
  rw [heq]
  refine hη.congr_deriv ?_
  have hIm := im_coneDisc_mul v z
  have hD0 : D 0 = normSq (z - conj v) := by rw [← hD 0]; simp
  rw [← hD0] at hIm
  rw [← hD0]
  have hDp := hDpos 0
  have : (coneDisc v z).im = 2 * v.im * (v.re - x) / D 0 := by
    rw [eq_div_iff hDp.ne']
    exact hIm
  rw [this]
  field_simp
  ring

theorem hasDerivAt_cuspZeroHeight_horizontal (z : ℂ) :
    HasDerivAt (fun t : ℝ => cuspZeroHeight (z + t)) (2 * z.re / z.im) 0 := by
  have h : (fun t : ℝ => cuspZeroHeight (z + t)) =
      fun t : ℝ => ((z.re + t) ^ 2 + z.im ^ 2) / z.im := by
    funext t
    simp [cuspZeroHeight, normSq_apply]
    ring
  rw [h]
  have := (((hasDerivAt_id' (0 : ℝ)).const_add z.re).pow 2 |>.add_const (z.im ^ 2)).div_const z.im
  convert this using 1
  simp

end GC.Seifert
