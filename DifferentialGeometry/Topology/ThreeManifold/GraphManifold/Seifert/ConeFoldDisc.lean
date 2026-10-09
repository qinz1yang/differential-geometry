import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Norm

/-!
# Disc coordinates at a point of the upper half-plane

Lane A4, tier 1 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §2).
For `v` in the upper half-plane, `coneDisc v z = (z - v)/(z - v̄)` is the Poincaré disc coordinate
centred at `v`: it vanishes at `v`, has modulus `< 1` on the upper half-plane
(`norm_coneDisc_lt_one`), the upward vertical direction goes to the positive reals, and the height
is `Im z = Im v (1 - |ω|²)/|1 - ω|²` (`im_eq_coneDisc`). The reflection in the vertical line
through `v` is `ω ↦ ω̄` (`coneDisc_vertical`), the reflection in a circle `|z - c| = 1/4`
through `v = c + e^{iψ}/4` is `ω ↦ e^{2iψ} ω̄` (`coneDisc_circle`). The side functions of these two
walls are, up to the positive factor `|z - v̄|²`, the imaginary parts of `ω` and of `e^{-iψ} ω`
(`im_coneDisc_mul`, `im_rot_coneDisc_mul`).

The virtual height `coneHeight v z = Im v (1 + |ω|)/(1 - |ω|) = Im v · e^{d(z, v)}` of a point
seen from `v` compares with the height `Im z` of the cusp `∞` and with the height
`|z|²/Im z` of the cusp `0` by exact second-order identities: `coneHeight_sub_im` and
`coneHeight_mul_cuspZero_sub`, in which the vanishing factor is the square of the imaginary part
of the (rotated) disc coordinate.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GC.Seifert

def coneDisc (v z : ℂ) : ℂ := (z - v) / (z - conj v)

theorem coneDisc_self (v : ℂ) : coneDisc v v = 0 := by
  simp [coneDisc]

theorem sub_conj_ne_zero {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) : z - conj v ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem normSq_sub_conj_pos {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    0 < normSq (z - conj v) :=
  normSq_pos.2 (sub_conj_ne_zero hv hz)

theorem normSq_sub_conj_eq (v z : ℂ) :
    normSq (z - conj v) = normSq (z - v) + 4 * z.im * v.im := by
  simp only [normSq_apply, sub_re, sub_im, conj_re, conj_im]
  ring

theorem normSq_coneDisc (v z : ℂ) :
    normSq (coneDisc v z) = normSq (z - v) / normSq (z - conj v) := by
  rw [coneDisc, map_div₀]

theorem one_sub_normSq_coneDisc {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    1 - normSq (coneDisc v z) = 4 * z.im * v.im / normSq (z - conj v) := by
  have hp := normSq_sub_conj_pos hv hz
  rw [normSq_coneDisc v z, normSq_sub_conj_eq v z] at *
  field_simp
  ring

theorem normSq_coneDisc_lt_one {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    normSq (coneDisc v z) < 1 := by
  have h := one_sub_normSq_coneDisc hv hz
  have hp := normSq_sub_conj_pos hv hz
  have : 0 < 4 * z.im * v.im / normSq (z - conj v) := by positivity
  linarith

theorem norm_coneDisc_lt_one {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    ‖coneDisc v z‖ < 1 := by
  have h := normSq_coneDisc_lt_one hv hz
  rw [← Complex.sq_norm] at h
  nlinarith [norm_nonneg (coneDisc v z)]

theorem one_sub_coneDisc {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    1 - coneDisc v z = (v - conj v) / (z - conj v) := by
  have h := sub_conj_ne_zero hv hz
  rw [coneDisc]
  field_simp
  ring

theorem normSq_one_sub_coneDisc {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    normSq (1 - coneDisc v z) = 4 * v.im ^ 2 / normSq (z - conj v) := by
  rw [one_sub_coneDisc hv hz, map_div₀]
  congr 1
  simp only [normSq_apply, sub_re, sub_im, conj_re, conj_im]
  ring

theorem im_eq_coneDisc {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    z.im = v.im * (1 - normSq (coneDisc v z)) / normSq (1 - coneDisc v z) := by
  have hp := normSq_sub_conj_pos hv hz
  rw [one_sub_normSq_coneDisc hv hz, normSq_one_sub_coneDisc hv hz]
  field_simp

theorem coneDisc_vertical (v z : ℂ) :
    coneDisc v (2 * (v.re : ℂ) - conj z) = conj (coneDisc v z) := by
  have h1 : 2 * (v.re : ℂ) - conj z - v = conj (v - z) := by
    apply Complex.ext <;> simp <;> ring
  have h2 : 2 * (v.re : ℂ) - conj z - conj v = conj (conj v - z) := by
    apply Complex.ext <;> simp <;> ring
  rw [coneDisc, coneDisc, h1, h2, ← map_div₀]
  congr 1
  rw [← neg_sub z v, ← neg_sub z (conj v), neg_div_neg_eq]

theorem im_coneDisc_mul (v z : ℂ) :
    (coneDisc v z).im * normSq (z - conj v) = 2 * v.im * (v.re - z.re) := by
  by_cases h : z - conj v = 0
  · have h1 : z.re = v.re := by simpa using congrArg Complex.re (sub_eq_zero.1 h)
    rw [h, map_zero, mul_zero, h1, sub_self, mul_zero]
  · have hp : normSq (z - conj v) ≠ 0 := normSq_eq_zero.not.2 h
    rw [coneDisc, div_im]
    field_simp
    simp only [sub_re, sub_im, conj_re, conj_im]
    ring

theorem coneDisc_mul_normSq (v z : ℂ) :
    coneDisc v z * (normSq (z - conj v) : ℂ) = (z - v) * conj (z - conj v) := by
  by_cases h : z - conj v = 0
  · simp [coneDisc, h]
  · rw [coneDisc, Complex.normSq_eq_conj_mul_self]
    field_simp

theorem coneDisc_circle_aux {c : ℝ} {u z : ℂ} (huu : u * conj u = 1 / 16)
    (hz : conj z - c ≠ 0) :
    coneDisc ((c : ℂ) + u) ((c : ℂ) + 1 / 16 / (conj z - c)) =
      u / conj u * conj (coneDisc ((c : ℂ) + u) z) := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at huu
  have hub : conj u ≠ 0 := (map_ne_zero _).2 hu
  simp only [coneDisc, map_div₀, map_sub, map_add, Complex.conj_ofReal, Complex.conj_conj]
  rw [← huu]
  set ζ := conj z - (c : ℂ) with hζdef
  have e1 : (c : ℂ) + u * conj u / ζ - ((c : ℂ) + u) = u * (conj u - ζ) / ζ := by
    field_simp
    ring
  have e2 : (c : ℂ) + u * conj u / ζ - ((c : ℂ) + conj u) = conj u * (u - ζ) / ζ := by
    field_simp
    ring
  have e3 : conj z - ((c : ℂ) + conj u) = ζ - conj u := by
    rw [hζdef]
    ring
  have e4 : conj z - ((c : ℂ) + u) = ζ - u := by
    rw [hζdef]
    ring
  rw [e1, e2, e3, e4]
  by_cases h : ζ - u = 0
  · have h' : u - ζ = 0 := by rw [← neg_sub, h, neg_zero]
    simp [h, h']
  · have h' : u - ζ ≠ 0 := by
      intro h''
      apply h
      rw [← neg_sub, h'', neg_zero]
    field_simp
    ring

theorem coneDisc_circle {c ψ : ℝ} {z : ℂ} (hz : z ≠ c) :
    coneDisc ((c : ℂ) + exp (ψ * I) / 4) ((c : ℂ) + 1 / 16 / (conj z - c)) =
      exp (2 * ψ * I) * conj (coneDisc ((c : ℂ) + exp (ψ * I) / 4) z) := by
  have hub : conj (exp (ψ * I) / 4) = exp (-(ψ * I)) / 4 := by
    rw [map_div₀, ← Complex.exp_conj, map_ofNat]
    simp
  have huu : exp (ψ * I) / 4 * conj (exp (ψ * I) / 4) = 1 / 16 := by
    rw [hub, div_mul_div_comm, ← Complex.exp_add]
    simp
    norm_num
  have hζ : conj z - c ≠ 0 := by
    intro h
    apply hz
    have : conj z = c := sub_eq_zero.1 h
    rw [← Complex.conj_conj z, this, Complex.conj_ofReal]
  rw [coneDisc_circle_aux huu hζ, hub]
  congr 1
  rw [div_div_div_cancel_right₀ (by norm_num : (4 : ℂ) ≠ 0), div_eq_iff (Complex.exp_ne_zero _),
    ← Complex.exp_add]
  congr 1
  ring

theorem im_rot_coneDisc_mul (c ψ : ℝ) (z : ℂ) :
    (exp (-(ψ * I)) * coneDisc ((c : ℂ) + exp (ψ * I) / 4) z).im *
        normSq (z - conj ((c : ℂ) + exp (ψ * I) / 4)) =
      -Real.sin ψ * ((z.re - c) ^ 2 + z.im ^ 2 - 1 / 16) := by
  have h := coneDisc_mul_normSq ((c : ℂ) + exp (ψ * I) / 4) z
  have h2 : (exp (-(ψ * I)) * coneDisc ((c : ℂ) + exp (ψ * I) / 4) z).im *
      normSq (z - conj ((c : ℂ) + exp (ψ * I) / 4)) =
      (exp (-(ψ * I)) * (coneDisc ((c : ℂ) + exp (ψ * I) / 4) z *
        (normSq (z - conj ((c : ℂ) + exp (ψ * I) / 4)) : ℂ))).im := by
    rw [← mul_assoc, Complex.mul_im (cexp _ * _) _, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h2, h]
  have hn : exp (-(ψ * I)) = (Real.cos ψ : ℂ) - (Real.sin ψ : ℂ) * I := by
    rw [show -(ψ * I) = ((-ψ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  have hp : exp ((ψ : ℂ) * I) = (Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * I := by
    rw [Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hn, hp]
  simp only [map_sub, map_add, map_div₀, Complex.conj_ofReal, map_mul,
    Complex.conj_I, map_ofNat]
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.neg_re,
    Complex.neg_im]
  have hs := Real.sin_sq_add_cos_sq ψ
  linear_combination (1 / 16 * Real.sin ψ) * hs

theorem mul_one_sub_coneDisc {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    z * (1 - coneDisc v z) = v - conj v * coneDisc v z := by
  have h := sub_conj_ne_zero hv hz
  rw [coneDisc]
  field_simp
  ring

def coneHeight (v z : ℂ) : ℝ := v.im * (1 + ‖coneDisc v z‖) / (1 - ‖coneDisc v z‖)

def cuspZeroHeight (z : ℂ) : ℝ := normSq z / z.im

theorem coneHeight_pos {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) : 0 < coneHeight v z := by
  have h := norm_coneDisc_lt_one hv hz
  have h0 := norm_nonneg (coneDisc v z)
  unfold coneHeight
  apply div_pos _ (by linarith)
  positivity

theorem cuspZeroHeight_eq_coneDisc {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    cuspZeroHeight z =
      normSq (v - conj v * coneDisc v z) / (v.im * (1 - normSq (coneDisc v z))) := by
  have hN : normSq (1 - coneDisc v z) ≠ 0 := by
    rw [normSq_one_sub_coneDisc hv hz]
    have := normSq_sub_conj_pos hv hz
    positivity
  have hr : 1 - normSq (coneDisc v z) ≠ 0 := (sub_pos.2 (normSq_coneDisc_lt_one hv hz)).ne'
  have h1 : normSq z = normSq (v - conj v * coneDisc v z) / normSq (1 - coneDisc v z) := by
    rw [← mul_one_sub_coneDisc hv hz, map_mul]
    field_simp
  rw [cuspZeroHeight, h1, im_eq_coneDisc hv hz]
  field_simp

theorem height_identity_inf (a r X Y : ℝ) (hr : r ^ 2 = X ^ 2 + Y ^ 2) (hr1 : r < 1)
    (hrX : 0 < r + X) :
    a * (1 + r) / (1 - r) - a * (1 - r ^ 2) / ((1 - X) ^ 2 + Y ^ 2) =
      2 * a * (1 - r ^ 2) * Y ^ 2 / ((r + X) * (1 - r) ^ 2 * ((1 - X) ^ 2 + Y ^ 2)) := by
  have h1 : 0 < 1 - r := by linarith
  have hX : X < 1 := by nlinarith [sq_nonneg Y]
  have hN : 0 < (1 - X) ^ 2 + Y ^ 2 := by
    have : 0 < (1 - X) ^ 2 := by nlinarith
    positivity
  rw [div_sub_div _ _ h1.ne' hN.ne', div_eq_div_iff (by positivity) (by positivity)]
  have hY : Y ^ 2 = (r - X) * (r + X) := by nlinarith
  rw [hY]
  ring_nf

theorem coneHeight_sub_im {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im)
    (hX : 0 < ‖coneDisc v z‖ + (coneDisc v z).re) :
    coneHeight v z - z.im =
      2 * v.im * (1 - ‖coneDisc v z‖ ^ 2) * (coneDisc v z).im ^ 2 /
        ((‖coneDisc v z‖ + (coneDisc v z).re) * (1 - ‖coneDisc v z‖) ^ 2 *
          ((1 - (coneDisc v z).re) ^ 2 + (coneDisc v z).im ^ 2)) := by
  set ω := coneDisc v z with hω
  have hr : ‖ω‖ ^ 2 = ω.re ^ 2 + ω.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    ring
  have hN : normSq (1 - ω) = (1 - ω.re) ^ 2 + ω.im ^ 2 := by
    rw [normSq_apply]
    simp
    ring
  have him := im_eq_coneDisc hv hz
  rw [← hω, hN, ← Complex.sq_norm] at him
  rw [coneHeight, ← hω, him]
  exact height_identity_inf v.im ‖ω‖ ω.re ω.im hr (norm_coneDisc_lt_one hv hz) hX

theorem height_identity_zero (r X Y : ℝ) (hr : r ^ 2 = X ^ 2 + Y ^ 2) (hr1 : r < 1)
    (hrX : 0 < r + X) :
    (1 + r) / (1 - r) * (((1 - X) ^ 2 + Y ^ 2) / (1 - r ^ 2)) - 1 =
      2 * Y ^ 2 / ((r + X) * (1 - r) ^ 2) := by
  have h1 : 0 < 1 - r := by linarith
  have h2 : 0 < 1 + r := by nlinarith [sq_nonneg X, sq_nonneg Y]
  have h3 : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [h3]
  field_simp
  have hY : Y ^ 2 = (r - X) * (r + X) := by nlinarith
  rw [hY]
  ring_nf

theorem normSq_rot (v ω : ℂ) (hv : v ≠ 0) : normSq (conj v / v * ω) = normSq ω := by
  rw [map_mul, map_div₀, Complex.normSq_conj, div_self (normSq_eq_zero.not.2 hv), one_mul]

theorem coneHeight_mul_cuspZero_sub {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im)
    (hX : 0 < ‖coneDisc v z‖ + (conj v / v * coneDisc v z).re) :
    coneHeight v z * cuspZeroHeight z - normSq v =
      normSq v * (2 * (conj v / v * coneDisc v z).im ^ 2 /
        ((‖coneDisc v z‖ + (conj v / v * coneDisc v z).re) * (1 - ‖coneDisc v z‖) ^ 2)) := by
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  set ω := coneDisc v z with hω
  set ω' := conj v / v * ω with hω'
  have hn : ‖ω'‖ = ‖ω‖ := by
    rw [← Real.sqrt_sq (norm_nonneg ω'), ← Real.sqrt_sq (norm_nonneg ω), Complex.sq_norm,
      Complex.sq_norm, hω', normSq_rot v ω hv0]
  have hr : ‖ω‖ ^ 2 = ω'.re ^ 2 + ω'.im ^ 2 := by
    rw [← hn, Complex.sq_norm, normSq_apply]
    ring
  have hvw : v - conj v * ω = v * (1 - ω') := by
    rw [hω']
    field_simp
  have hN : normSq (1 - ω') = (1 - ω'.re) ^ 2 + ω'.im ^ 2 := by
    rw [normSq_apply]
    simp
    ring
  have hc := cuspZeroHeight_eq_coneDisc hv hz
  rw [← hω, hvw, map_mul, hN] at hc
  simp only [← Complex.sq_norm] at hc
  have hr1 := norm_coneDisc_lt_one hv hz
  rw [← hω] at hr1
  have hid := height_identity_zero ‖ω‖ ω'.re ω'.im hr hr1 hX
  have h1 : 0 < 1 - ‖ω‖ := by linarith
  have h2 : 0 < 1 - ‖ω‖ ^ 2 := by nlinarith [norm_nonneg ω]
  rw [coneHeight, ← hω, hc, ← hid, ← Complex.sq_norm v]
  field_simp

theorem coneDisc_sub_coneDisc {v w z : ℂ} (hv : 0 < v.im) (hw : 0 < w.im) (hz : 0 < z.im) :
    coneDisc v z - coneDisc v w =
      -(coneDisc w z * ((conj w - v) / (w - conj v)) *
        (1 - conj (coneDisc v w) * coneDisc v z)) := by
  have h1 := sub_conj_ne_zero hv hz
  have h2 := sub_conj_ne_zero hv hw
  have h3 : conj w - v ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h4 := sub_conj_ne_zero hw hz
  simp only [coneDisc, map_div₀, map_sub, Complex.conj_conj]
  field_simp
  ring

theorem norm_conj_sub_div {v w : ℂ} (hv : 0 < v.im) (hw : 0 < w.im) :
    ‖(conj w - v) / (w - conj v)‖ = 1 := by
  have h2 := sub_conj_ne_zero hv hw
  have : conj w - v = conj (w - conj v) := by simp
  rw [this, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h2)]

theorem norm_coneDisc_moebius {v w z : ℂ} (hv : 0 < v.im) (hw : 0 < w.im) (hz : 0 < z.im) :
    ‖coneDisc w z‖ * ‖1 - conj (coneDisc v w) * coneDisc v z‖ =
      ‖coneDisc v z - coneDisc v w‖ := by
  rw [coneDisc_sub_coneDisc hv hw hz, norm_neg, norm_mul, norm_mul, norm_conj_sub_div hv hw,
    mul_one]

theorem product_identity_two (a b r μ t : ℝ) (hr : r < 1) (hμ : μ < 1) (ht : t < 1) :
    a * (1 + r) / (1 - r) * (b * (1 + μ) / (1 - μ)) - a * b * (1 + t) / (1 - t) =
      2 * a * b / (1 - t) * ((r + μ - t * (1 + r * μ)) / ((1 - r) * (1 - μ))) := by
  have h1 : 1 - r ≠ 0 := by linarith
  have h2 : 1 - μ ≠ 0 := by linarith
  have h3 : 1 - t ≠ 0 := by linarith
  field_simp
  ring

theorem bracket_identity (r μ t X Y : ℝ) (hr : r ^ 2 = X ^ 2 + Y ^ 2)
    (hμ : μ ^ 2 * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) = (X - t) ^ 2 + Y ^ 2)
    (hrX : 0 < r + X) (htX : 0 < 1 - t * X)
    (hμμ : 0 < μ + (t - X) / (1 - t * X)) :
    r + μ - t * (1 + r * μ) =
      Y ^ 2 * ((1 - t * μ) / (r + X) + (1 - t ^ 2) * (1 - 2 * t * X + t ^ 2) /
        ((1 - t * X) * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) * (μ + (t - X) / (1 - t * X)))) := by
  set μ₀ := (t - X) / (1 - t * X) with hμ₀
  have hD : 0 < (1 - t * X) ^ 2 + t ^ 2 * Y ^ 2 := by positivity
  have htX' : 1 - t * X ≠ 0 := htX.ne'
  have hD' : (1 - t * X) ^ 2 + t ^ 2 * Y ^ 2 ≠ 0 := hD.ne'
  have hμ₀' : μ₀ * (1 - t * X) = t - X := by
    rw [hμ₀]
    field_simp
  have e1 : r - X = Y ^ 2 / (r + X) := by
    rw [eq_div_iff hrX.ne']
    nlinarith
  have hsq : μ ^ 2 - μ₀ ^ 2 =
      Y ^ 2 * (1 - t ^ 2) * (1 - 2 * t * X + t ^ 2) /
        ((1 - t * X) ^ 2 * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2)) := by
    have hm : μ ^ 2 = ((X - t) ^ 2 + Y ^ 2) / ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) := by
      rw [eq_div_iff hD.ne']
      exact hμ
    rw [hm, hμ₀, div_pow, div_sub_div _ _ hD' (pow_ne_zero 2 htX'),
      div_eq_div_iff (mul_ne_zero hD' (pow_ne_zero 2 htX'))
        (mul_ne_zero (pow_ne_zero 2 htX') hD')]
    ring
  have e2 : μ - μ₀ =
      Y ^ 2 * (1 - t ^ 2) * (1 - 2 * t * X + t ^ 2) /
        ((1 - t * X) ^ 2 * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) * (μ + μ₀)) := by
    rw [← div_div, ← hsq, eq_div_iff hμμ.ne']
    ring
  have key : r + μ - t * (1 + r * μ) = (r - X) * (1 - t * μ) + (μ - μ₀) * (1 - t * X) := by
    linear_combination hμ₀'
  rw [key, e1, e2]
  field_simp

end GC.Seifert
