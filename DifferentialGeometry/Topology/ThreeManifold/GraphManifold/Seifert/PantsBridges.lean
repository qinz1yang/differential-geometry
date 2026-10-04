import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFold
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Bipolar bridges between the cusp families of the pants map

Packet K16f, tier 2 (definitions and algebra). In real coordinates `z = x + iy` of the upper
half-plane, `heightOne x y = y / (4 |z|²)` is the height of the cusp `0` (the imaginary part of
`-1/(4z)`, whose real part is `holeX x y`), `heightOne (1/2 - x) y` that of the cusp `1/2`, and
`y` that of the cusp `∞`; `holeInvRe`, `holeInvIm` invert `z ↦ -1/(4z)`. The radial profiles
`bridgeSigma t = 1/2 + 2/(1 + 4t²)` (holes) and `bridgeRho t = 4 - 2/(1 + 4t²)` (outer end)
satisfy `bridgeRho y = 3/2 + bridgeSigma (1/(4y))` and `bridgeSigma t + bridgeSigma (1/(4t)) = 3`.

The bridge `bridgeZero` is the point `u` with `|u| = bridgeRho y` and
`|u - 3/2| = bridgeSigma (heightOne x y)`, of imaginary part of the sign of `x`: since
`3/2 - bridgeRho y + bridgeSigma (heightOne x y) = x² bridgeP0 x y` with `bridgeP0 > 0`
(`bridge_identity_zero`), its imaginary part is `x √(bridgeQ0 x y)` with `bridgeQ0 > 0`
explicit, so it is given by an explicit smooth formula. Likewise `bridgeTwo` is the point with
`|u ∓ 3/2| = bridgeSigma (heightOne x y), bridgeSigma (heightOne (1/2 - x) y)`, of imaginary
part `wallTwo x y √(bridgeQ2 x y)` (`bridge_identity_two`), `wallTwo` the side function of the
semicircle wall. `angleZero`, `angleZeroHole` and `angleTwoHole` are the arguments of
`bridgeZero`, `bridgeZero - 3/2` and `bridgeTwo - 3/2`, written with `arctan`; the derivative of
such an angle along a line on which the modulus is constant is computed in
`hasDerivAt_arctan_div` and `arctan_div_deriv_eq`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace GC.Seifert

def bridgeSigma (t : ℝ) : ℝ := 1 / 2 + 2 / (1 + 4 * t ^ 2)

def bridgeRho (t : ℝ) : ℝ := 4 - 2 / (1 + 4 * t ^ 2)

def heightOne (x y : ℝ) : ℝ := y / (4 * (x ^ 2 + y ^ 2))

def holeX (x y : ℝ) : ℝ := -x / (4 * (x ^ 2 + y ^ 2))

def holeInvRe (X Y : ℝ) : ℝ := -X / (4 * (X ^ 2 + Y ^ 2))

def holeInvIm (X Y : ℝ) : ℝ := Y / (4 * (X ^ 2 + Y ^ 2))

def wallTwo (x y : ℝ) : ℝ := x ^ 2 + y ^ 2 - x / 2

def bridgeP0 (x y : ℝ) : ℝ :=
  8 * (x ^ 2 + 2 * y ^ 2) / ((1 + 4 * y ^ 2) * (4 * (x ^ 2 + y ^ 2) ^ 2 + y ^ 2))

def bridgeQ0 (x y : ℝ) : ℝ :=
  bridgeP0 x y * (3 / 2 + bridgeRho y - bridgeSigma (heightOne x y)) *
    ((bridgeRho y + bridgeSigma (heightOne x y)) ^ 2 - 9 / 4) / 9

def bridgeRe0 (x y : ℝ) : ℝ :=
  (bridgeRho y ^ 2 - bridgeSigma (heightOne x y) ^ 2 + 9 / 4) / 3

def bridgeIm0 (x y : ℝ) : ℝ := x * Real.sqrt (bridgeQ0 x y)

def bridgeP2 (x y : ℝ) : ℝ :=
  8 * (4 * ((1 / 2 - x) ^ 2 + y ^ 2) * (x ^ 2 + y ^ 2) + y ^ 2) /
    ((4 * ((1 / 2 - x) ^ 2 + y ^ 2) ^ 2 + y ^ 2) * (4 * (x ^ 2 + y ^ 2) ^ 2 + y ^ 2))

def bridgeQ2 (x y : ℝ) : ℝ :=
  bridgeP2 x y * (bridgeSigma (heightOne (1 / 2 - x) y) + bridgeSigma (heightOne x y) + 3) *
    (9 - (bridgeSigma (heightOne (1 / 2 - x) y) - bridgeSigma (heightOne x y)) ^ 2) / 36

def bridgeRe2 (x y : ℝ) : ℝ :=
  (bridgeSigma (heightOne (1 / 2 - x) y) ^ 2 - bridgeSigma (heightOne x y) ^ 2) / 6

def bridgeIm2 (x y : ℝ) : ℝ := wallTwo x y * Real.sqrt (bridgeQ2 x y)

def bridgeZero (z : ℂ) : ℂ := ⟨bridgeRe0 z.re z.im, bridgeIm0 z.re z.im⟩

def bridgeTwo (z : ℂ) : ℂ := ⟨bridgeRe2 z.re z.im, bridgeIm2 z.re z.im⟩

def angleZero (x y : ℝ) : ℝ := Real.arctan (bridgeIm0 x y / bridgeRe0 x y)

def angleZeroHole (x y : ℝ) : ℝ := Real.arctan (bridgeIm0 x y / (bridgeRe0 x y - 3 / 2))

def angleTwoHole (x y : ℝ) : ℝ :=
  Real.pi - Real.arctan (bridgeIm2 x y / (3 / 2 - bridgeRe2 x y))

theorem bridgeZero_re (z : ℂ) : (bridgeZero z).re = bridgeRe0 z.re z.im := rfl

theorem bridgeZero_im (z : ℂ) : (bridgeZero z).im = bridgeIm0 z.re z.im := rfl

theorem bridgeTwo_re (z : ℂ) : (bridgeTwo z).re = bridgeRe2 z.re z.im := rfl

theorem bridgeTwo_im (z : ℂ) : (bridgeTwo z).im = bridgeIm2 z.re z.im := rfl

theorem two_le_bridgeRho (t : ℝ) : 2 ≤ bridgeRho t := by
  unfold bridgeRho
  have : 2 / (1 + 4 * t ^ 2) ≤ 2 := div_le_self (by norm_num) (by nlinarith)
  linarith

theorem two_lt_bridgeRho {t : ℝ} (ht : t ≠ 0) : 2 < bridgeRho t := by
  unfold bridgeRho
  have h1 : 1 < 1 + 4 * t ^ 2 := by have := pow_pos (abs_pos.2 ht) 2; rw [sq_abs] at this; linarith
  have : 2 / (1 + 4 * t ^ 2) < 2 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  linarith

theorem bridgeRho_lt_four (t : ℝ) : bridgeRho t < 4 := by
  unfold bridgeRho
  have : 0 < 2 / (1 + 4 * t ^ 2) := by positivity
  linarith

theorem half_lt_bridgeSigma (t : ℝ) : 1 / 2 < bridgeSigma t := by
  unfold bridgeSigma
  have : 0 < 2 / (1 + 4 * t ^ 2) := by positivity
  linarith

theorem bridgeSigma_le (t : ℝ) : bridgeSigma t ≤ 5 / 2 := by
  unfold bridgeSigma
  have : 2 / (1 + 4 * t ^ 2) ≤ 2 := div_le_self (by norm_num) (by nlinarith)
  linarith

theorem heightOne_pos {x y : ℝ} (hy : 0 < y) : 0 < heightOne x y := by
  unfold heightOne
  positivity

theorem holeInvIm_pos {X Y : ℝ} (hY : 0 < Y) : 0 < holeInvIm X Y := by
  unfold holeInvIm
  positivity

theorem heightOne_holeInv {X Y : ℝ} (hY : 0 < Y) :
    heightOne (holeInvRe X Y) (holeInvIm X Y) = Y := by
  have hs : 0 < X ^ 2 + Y ^ 2 := by positivity
  unfold heightOne holeInvRe holeInvIm
  field_simp

theorem holeX_holeInv {X Y : ℝ} (hY : 0 < Y) :
    holeX (holeInvRe X Y) (holeInvIm X Y) = X := by
  have hs : 0 < X ^ 2 + Y ^ 2 := by positivity
  unfold holeX holeInvRe holeInvIm
  field_simp

theorem holeInv_holeX {x y : ℝ} (hy : 0 < y) :
    holeInvRe (holeX x y) (heightOne x y) = x ∧ holeInvIm (holeX x y) (heightOne x y) = y := by
  have hs : 0 < x ^ 2 + y ^ 2 := by positivity
  unfold holeX heightOne holeInvRe holeInvIm
  constructor
  · field_simp
  · field_simp

theorem bridge_identity_zero {x y : ℝ} (hy : 0 < y) :
    3 / 2 - bridgeRho y + bridgeSigma (heightOne x y) = x ^ 2 * bridgeP0 x y := by
  have hs : 0 < x ^ 2 + y ^ 2 := by positivity
  unfold bridgeRho bridgeSigma heightOne bridgeP0
  field_simp
  ring

theorem bridge_identity_two {x y : ℝ} (hy : 0 < y) :
    bridgeSigma (heightOne (1 / 2 - x) y) + bridgeSigma (heightOne x y) - 3 =
      wallTwo x y ^ 2 * bridgeP2 x y := by
  have hs : 0 < x ^ 2 + y ^ 2 := by positivity
  have hs' : 0 < (1 / 2 - x) ^ 2 + y ^ 2 := by positivity
  unfold bridgeSigma heightOne bridgeP2 wallTwo
  field_simp
  ring

theorem bridgeP0_pos {x y : ℝ} (hy : 0 < y) : 0 < bridgeP0 x y := by
  unfold bridgeP0
  positivity

theorem bridgeQ0_pos {x y : ℝ} (hy : 0 < y) : 0 < bridgeQ0 x y := by
  unfold bridgeQ0
  have h1 := two_le_bridgeRho y
  have h2 := bridgeSigma_le (heightOne x y)
  have h3 := half_lt_bridgeSigma (heightOne x y)
  have h4 : 0 < 3 / 2 + bridgeRho y - bridgeSigma (heightOne x y) := by linarith
  have h5 : 0 < (bridgeRho y + bridgeSigma (heightOne x y)) ^ 2 - 9 / 4 := by nlinarith
  have := bridgeP0_pos (x := x) hy
  positivity

theorem bridgeP2_pos {x y : ℝ} (hy : 0 < y) : 0 < bridgeP2 x y := by
  unfold bridgeP2
  positivity

theorem bridgeQ2_pos {x y : ℝ} (hy : 0 < y) : 0 < bridgeQ2 x y := by
  unfold bridgeQ2
  have h1 := bridgeSigma_le (heightOne (1 / 2 - x) y)
  have h2 := bridgeSigma_le (heightOne x y)
  have h3 := half_lt_bridgeSigma (heightOne (1 / 2 - x) y)
  have h4 := half_lt_bridgeSigma (heightOne x y)
  have h5 : 0 < 9 - (bridgeSigma (heightOne (1 / 2 - x) y) - bridgeSigma (heightOne x y)) ^ 2 := by
    nlinarith
  have := bridgeP2_pos (x := x) hy
  have h6 : 0 < bridgeSigma (heightOne (1 / 2 - x) y) + bridgeSigma (heightOne x y) + 3 := by
    linarith
  positivity

theorem bridgeRe0_sq_add_bridgeIm0_sq {x y : ℝ} (hy : 0 < y) :
    bridgeRe0 x y ^ 2 + bridgeIm0 x y ^ 2 = bridgeRho y ^ 2 := by
  have hq := (bridgeQ0_pos (x := x) hy).le
  have hI := bridge_identity_zero (x := x) hy
  rw [bridgeIm0, mul_pow, Real.sq_sqrt hq, bridgeRe0, bridgeQ0]
  set a := bridgeRho y
  set b := bridgeSigma (heightOne x y)
  linear_combination ((1 / 9) * (3 / 2 + a - b) * ((a + b) ^ 2 - 9 / 4)) * hI.symm

theorem bridgeRe0_sub_sq_add_bridgeIm0_sq {x y : ℝ} (hy : 0 < y) :
    (bridgeRe0 x y - 3 / 2) ^ 2 + bridgeIm0 x y ^ 2 = bridgeSigma (heightOne x y) ^ 2 := by
  have h := bridgeRe0_sq_add_bridgeIm0_sq (x := x) hy
  have : (bridgeRe0 x y - 3 / 2) ^ 2 + bridgeIm0 x y ^ 2 =
      bridgeRe0 x y ^ 2 + bridgeIm0 x y ^ 2 - 3 * bridgeRe0 x y + 9 / 4 := by ring
  rw [this, h, bridgeRe0]
  ring

theorem bridgeRe2_sub_sq_add_bridgeIm2_sq {x y : ℝ} (hy : 0 < y) :
    (bridgeRe2 x y - 3 / 2) ^ 2 + bridgeIm2 x y ^ 2 = bridgeSigma (heightOne x y) ^ 2 := by
  have hq := (bridgeQ2_pos (x := x) hy).le
  have hI := bridge_identity_two (x := x) hy
  rw [bridgeIm2, mul_pow, Real.sq_sqrt hq, bridgeRe2, bridgeQ2]
  set a := bridgeSigma (heightOne (1 / 2 - x) y)
  set b := bridgeSigma (heightOne x y)
  linear_combination ((1 / 36) * (a + b + 3) * (9 - (a - b) ^ 2)) * hI.symm

theorem bridgeRe2_add_sq_add_bridgeIm2_sq {x y : ℝ} (hy : 0 < y) :
    (bridgeRe2 x y + 3 / 2) ^ 2 + bridgeIm2 x y ^ 2 =
      bridgeSigma (heightOne (1 / 2 - x) y) ^ 2 := by
  have h := bridgeRe2_sub_sq_add_bridgeIm2_sq (x := x) hy
  have : (bridgeRe2 x y + 3 / 2) ^ 2 + bridgeIm2 x y ^ 2 =
      (bridgeRe2 x y - 3 / 2) ^ 2 + bridgeIm2 x y ^ 2 + 6 * bridgeRe2 x y := by ring
  rw [this, h, bridgeRe2]
  ring

theorem bridgeRe0_pos {x y : ℝ} (hy : 0 < y) : 0 < bridgeRe0 x y := by
  unfold bridgeRe0
  have h1 := two_lt_bridgeRho hy.ne'
  have h2 := bridgeSigma_le (heightOne x y)
  have h3 := half_lt_bridgeSigma (heightOne x y)
  nlinarith

theorem bridgeRe2_lt (x y : ℝ) : bridgeRe2 x y < 3 / 2 := by
  unfold bridgeRe2
  have h1 := bridgeSigma_le (heightOne (1 / 2 - x) y)
  have h3 := half_lt_bridgeSigma (heightOne (1 / 2 - x) y)
  have h4 := half_lt_bridgeSigma (heightOne x y)
  nlinarith

theorem hasDerivAt_arctan_div {R I : ℝ → ℝ} {R' I' t : ℝ} (hR : HasDerivAt R R' t)
    (hI : HasDerivAt I I' t) (hR0 : R t ≠ 0) :
    HasDerivAt (fun s => Real.arctan (I s / R s))
      ((R t * I' - I t * R') / (R t ^ 2 + I t ^ 2)) t := by
  have h := (hI.div hR hR0).arctan
  simp only [Pi.div_apply] at h
  convert h using 1
  field_simp

theorem arctan_div_deriv_eq {R I : ℝ → ℝ} {R' I' t K : ℝ} (hR : HasDerivAt R R' t)
    (hI : HasDerivAt I I' t) (hK : ∀ s, R s ^ 2 + I s ^ 2 = K) (hI0 : I t ≠ 0) :
    (R t * I' - I t * R') / (R t ^ 2 + I t ^ 2) = -R' / I t := by
  have hd : HasDerivAt (fun s => R s ^ 2 + I s ^ 2) (2 * R t * R' + 2 * I t * I') t := by
    convert (hR.pow 2).add (hI.pow 2) using 1
    simp
  have hc : HasDerivAt (fun s => R s ^ 2 + I s ^ 2) 0 t := by
    have : (fun s => R s ^ 2 + I s ^ 2) = Function.const ℝ K := funext hK
    rw [this]
    exact hasDerivAt_const t K
  have h0 := hd.unique hc
  have hpos : R t ^ 2 + I t ^ 2 ≠ 0 :=
    (lt_of_lt_of_le (sq_pos_of_ne_zero hI0) (le_add_of_nonneg_left (sq_nonneg _))).ne'
  rw [div_eq_div_iff hpos hI0]
  linear_combination (R t / 2) * h0

end GC.Seifert
