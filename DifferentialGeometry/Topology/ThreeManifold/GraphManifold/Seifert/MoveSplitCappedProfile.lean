import DifferentialGeometry.Topology.Manifold.ChartDisk.Construction
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels

/-!
# Profiles of the split sphere

Lane N2c, tier 1 (real profiles). The split sphere of a split seam is swept, level by level, by
a meridian profile: the latitude `x₃` of the round sphere goes to the seam height
`4 √(1 - x₃²) - 2` near the two junction circles `x₃ = ± √3 / 2`, and to a signed host radius
in between. `smoothSign` is the smooth sign (`-1` below `-1/2`, `1` above `1/2`, odd);
`hostRadius l r` is the radius at collar height `r` of the round pants circle `l` in its host
chart (`3 - r/4` for the outer circle, `4 / (2 + r)` after inversion about a hole), and
`bandHeight l x₃ = smoothSign x₃ · hostRadius l (4 √(1 - x₃²) - 2)`. Its derivative is positive
on `(-1, 1)` (`hasDerivAt_bandHeight`, `bandHeight_deriv_pos`), so it is strictly increasing
there and a local diffeomorphism of the line (`isLocalDiffeomorphAt_bandHeight`).
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Topology.Manifold
  (isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv)

namespace GC.Seifert.SplitTube

theorem smoothTransition_one_sub (y : ℝ) :
    Real.smoothTransition (1 - y) = 1 - Real.smoothTransition y := by
  unfold Real.smoothTransition
  have hd := (Real.smoothTransition.pos_denom y).ne'
  rw [sub_sub_cancel, add_comm (expNegInvGlue (1 - y)) (expNegInvGlue y), eq_sub_iff_add_eq,
    ← add_div, div_eq_one_iff_eq hd]
  ring

theorem smoothTransition_deriv_nonneg' (y : ℝ) : 0 ≤ deriv Real.smoothTransition y := by
  rw [(DifferentialGeometry.Topology.smoothTransition_hasDerivAt y).deriv]
  have h1 := expNegInvGlue.nonneg y
  have h2 := expNegInvGlue.nonneg (1 - y)
  positivity

def smoothSign (x : ℝ) : ℝ := 2 * Real.smoothTransition (x + 1 / 2) - 1

theorem contDiff_smoothSign : ContDiff ℝ ∞ smoothSign :=
  (contDiff_const.mul (Real.smoothTransition.contDiff.comp
    (contDiff_id.add contDiff_const))).sub contDiff_const

theorem smoothSign_of_ge {x : ℝ} (hx : 1 / 2 ≤ x) : smoothSign x = 1 := by
  rw [smoothSign, Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

theorem smoothSign_of_le {x : ℝ} (hx : x ≤ -1 / 2) : smoothSign x = -1 := by
  rw [smoothSign, Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

theorem smoothSign_neg (x : ℝ) : smoothSign (-x) = -smoothSign x := by
  have h : -x + 1 / 2 = 1 - (x + 1 / 2) := by ring
  rw [smoothSign, smoothSign, h, smoothTransition_one_sub]
  ring

theorem smoothSign_zero : smoothSign 0 = 0 := by
  have h := smoothSign_neg 0
  rw [neg_zero] at h
  linarith

theorem smoothSign_mono : Monotone smoothSign := fun x y hxy => by
  have := Real.smoothTransition.monotone (show x + 1 / 2 ≤ y + 1 / 2 by linarith)
  unfold smoothSign
  linarith

theorem smoothSign_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ smoothSign x :=
  smoothSign_zero ▸ smoothSign_mono hx

theorem smoothSign_nonpos {x : ℝ} (hx : x ≤ 0) : smoothSign x ≤ 0 :=
  smoothSign_zero ▸ smoothSign_mono hx

theorem mul_smoothSign_nonneg (x : ℝ) : 0 ≤ x * smoothSign x := by
  rcases le_total 0 x with hx | hx
  · exact mul_nonneg hx (smoothSign_nonneg hx)
  · exact mul_nonneg_of_nonpos_of_nonpos hx (smoothSign_nonpos hx)

theorem abs_smoothSign_le (x : ℝ) : |smoothSign x| ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (x + 1 / 2)
  have h1 := Real.smoothTransition.le_one (x + 1 / 2)
  rw [abs_le]
  unfold smoothSign
  constructor <;> linarith

theorem hasDerivAt_smoothSign (x : ℝ) :
    HasDerivAt smoothSign (2 * deriv Real.smoothTransition (x + 1 / 2)) x := by
  have h : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (x + 1 / 2))
      (x + 1 / 2) :=
    ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by norm_num) _).hasDerivAt
  have h2 := ((h.comp x ((hasDerivAt_id x).add_const (1 / 2))).const_mul 2).sub_const 1
  convert h2 using 1
  · funext y
    simp [smoothSign]
  · ring

theorem smoothSign_deriv_nonneg (x : ℝ) : 0 ≤ 2 * deriv Real.smoothTransition (x + 1 / 2) := by
  have := smoothTransition_deriv_nonneg' (x + 1 / 2)
  positivity

theorem smoothSign_deriv_pos {x : ℝ} (hx : |x| < 1 / 2) :
    0 < 2 * deriv Real.smoothTransition (x + 1 / 2) := by
  rw [abs_lt] at hx
  have := DifferentialGeometry.Topology.smoothTransition_deriv_pos
    (show 0 < x + 1 / 2 by linarith) (show x + 1 / 2 < 1 by linarith)
  positivity

def latRadius (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

theorem latRadius_pos {x : ℝ} (hx : |x| < 1) : 0 < latRadius x := by
  apply Real.sqrt_pos.mpr
  have : x ^ 2 < 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg x]
  linarith

theorem latRadius_le_one (x : ℝ) : latRadius x ≤ 1 := by
  rw [latRadius, Real.sqrt_le_one]
  nlinarith [sq_nonneg x]

theorem latRadius_sq {x : ℝ} (hx : |x| ≤ 1) : latRadius x ^ 2 = 1 - x ^ 2 := by
  rw [latRadius, Real.sq_sqrt]
  have : x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg x]
  linarith

theorem hasDerivAt_latRadius {x : ℝ} (hx : |x| < 1) :
    HasDerivAt latRadius (-x / latRadius x) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have hne : (1 : ℝ) - x ^ 2 ≠ 0 := by
    have := latRadius_pos hx
    rw [latRadius, Real.sqrt_pos] at this
    exact this.ne'
  have h2 := h1.sqrt hne
  convert h2 using 1
  · rfl
  · unfold latRadius
    rw [show -(2 * x) = 2 * -x by ring, mul_div_mul_left _ _ (two_ne_zero' ℝ)]

theorem contDiffAt_latRadius {x : ℝ} (hx : |x| < 1) : ContDiffAt ℝ ∞ latRadius x := by
  have h : (1 : ℝ) - x ^ 2 ≠ 0 := by
    have := latRadius_pos hx
    rw [latRadius, Real.sqrt_pos] at this
    exact this.ne'
  exact (contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt h

def seamHeight (x : ℝ) : ℝ := 4 * latRadius x - 2

def hostRadius (l : ℕ) (r : ℝ) : ℝ := if l = 0 then 3 - r / 4 else 4 / (2 + r)

def hostRadiusDeriv (l : ℕ) (r : ℝ) : ℝ := if l = 0 then -(1 / 4) else -4 / (2 + r) ^ 2

theorem hostRadius_pos (l : ℕ) {r : ℝ} (hr : -2 < r) (hr' : r < 12) : 0 < hostRadius l r := by
  unfold hostRadius
  split_ifs
  · linarith
  · apply div_pos (by norm_num)
    linarith

theorem hostRadiusDeriv_neg (l : ℕ) {r : ℝ} (hr : -2 < r) : hostRadiusDeriv l r < 0 := by
  unfold hostRadiusDeriv
  split_ifs
  · norm_num
  · apply div_neg_of_neg_of_pos (by norm_num)
    have : 0 < 2 + r := by linarith
    positivity

theorem hasDerivAt_hostRadius (l : ℕ) {r : ℝ} (hr : -2 < r) :
    HasDerivAt (hostRadius l) (hostRadiusDeriv l r) r := by
  unfold hostRadius hostRadiusDeriv
  split_ifs
  · simpa using ((hasDerivAt_id r).div_const 4).const_sub 3
  · have h2 : (2 : ℝ) + r ≠ 0 := by linarith
    have := ((hasDerivAt_id r).const_add 2).inv h2
    have h3 := this.const_mul 4
    convert h3 using 1
    · funext y
      simp [div_eq_mul_inv]
    · simp only [id]
      field_simp

theorem contDiffAt_hostRadius (l : ℕ) {r : ℝ} (hr : -2 < r) : ContDiffAt ℝ ∞ (hostRadius l) r := by
  unfold hostRadius
  split_ifs
  · exact contDiffAt_const.sub (contDiffAt_id.div_const 4)
  · exact contDiffAt_const.div (contDiffAt_const.add contDiffAt_id) (by linarith)

theorem seamHeight_gt {x : ℝ} (hx : |x| < 1) : -2 < seamHeight x := by
  have := latRadius_pos hx
  unfold seamHeight
  linarith

theorem seamHeight_le (x : ℝ) : seamHeight x ≤ 2 := by
  have := latRadius_le_one x
  unfold seamHeight
  linarith

def bandHeight (l : ℕ) (x : ℝ) : ℝ := smoothSign x * hostRadius l (seamHeight x)

def bandHeightDeriv (l : ℕ) (x : ℝ) : ℝ :=
  2 * deriv Real.smoothTransition (x + 1 / 2) * hostRadius l (seamHeight x) +
    smoothSign x * (hostRadiusDeriv l (seamHeight x) * (4 * (-x / latRadius x)))

theorem hasDerivAt_bandHeight (l : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (bandHeight l) (bandHeightDeriv l x) x := by
  have hs : HasDerivAt seamHeight (4 * (-x / latRadius x)) x := by
    change HasDerivAt (fun y => 4 * latRadius y - 2) _ x
    exact ((hasDerivAt_latRadius hx).const_mul 4).sub_const 2
  have hR := (hasDerivAt_hostRadius l (seamHeight_gt hx)).comp x hs
  exact (hasDerivAt_smoothSign x).mul hR

theorem bandHeightDeriv_pos (l : ℕ) {x : ℝ} (hx : |x| < 1) : 0 < bandHeightDeriv l x := by
  have hR := hostRadius_pos l (seamHeight_gt hx) (by linarith [seamHeight_le x])
  have hR' := hostRadiusDeriv_neg l (seamHeight_gt hx)
  have hL := latRadius_pos hx
  have hsd := smoothSign_deriv_nonneg x
  have hxs := mul_smoothSign_nonneg x
  have e : smoothSign x * (hostRadiusDeriv l (seamHeight x) * (4 * (-x / latRadius x))) =
      (x * smoothSign x) * (-hostRadiusDeriv l (seamHeight x)) * (4 / latRadius x) := by
    field_simp
  unfold bandHeightDeriv
  rw [e]
  have h2 : 0 ≤ (x * smoothSign x) * (-hostRadiusDeriv l (seamHeight x)) *
      (4 / latRadius x) := by
    have : 0 < -hostRadiusDeriv l (seamHeight x) := by linarith
    positivity
  by_cases hsmall : |x| < 1 / 2
  · have := smoothSign_deriv_pos hsmall
    have : 0 < 2 * deriv Real.smoothTransition (x + 1 / 2) * hostRadius l (seamHeight x) :=
      mul_pos this hR
    linarith
  · push Not at hsmall
    have hxs' : 0 < x * smoothSign x := by
      rcases le_or_gt 0 x with h0 | h0
      · rw [abs_of_nonneg h0] at hsmall
        rw [smoothSign_of_ge hsmall]
        linarith
      · rw [abs_of_neg h0] at hsmall
        rw [smoothSign_of_le (by linarith)]
        linarith
    have : 0 < (x * smoothSign x) * (-hostRadiusDeriv l (seamHeight x)) *
        (4 / latRadius x) := by
      have : 0 < -hostRadiusDeriv l (seamHeight x) := by linarith
      positivity
    have : 0 ≤ 2 * deriv Real.smoothTransition (x + 1 / 2) * hostRadius l (seamHeight x) :=
      mul_nonneg hsd hR.le
    linarith

theorem contDiffAt_bandHeight (l : ℕ) {x : ℝ} (hx : |x| < 1) :
    ContDiffAt ℝ ∞ (bandHeight l) x := by
  have hs : ContDiffAt ℝ ∞ seamHeight x :=
    (contDiffAt_const.mul (contDiffAt_latRadius hx)).sub contDiffAt_const
  exact contDiff_smoothSign.contDiffAt.mul
    ((contDiffAt_hostRadius l (seamHeight_gt hx)).comp x hs)

theorem strictMonoOn_bandHeight (l : ℕ) : StrictMonoOn (bandHeight l) (Ioo (-1) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo (-1) 1) ?_ ?_
  · intro x hx
    have hx' : |x| < 1 := abs_lt.mpr hx
    exact (hasDerivAt_bandHeight l hx').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    have hx' : |x| < 1 := abs_lt.mpr hx
    rw [(hasDerivAt_bandHeight l hx').deriv]
    exact bandHeightDeriv_pos l hx'

theorem bandHeight_of_ge (l : ℕ) {x : ℝ} (hx : 1 / 2 ≤ x) :
    bandHeight l x = hostRadius l (seamHeight x) := by
  rw [bandHeight, smoothSign_of_ge hx, one_mul]

theorem bandHeight_of_le (l : ℕ) {x : ℝ} (hx : x ≤ -1 / 2) :
    bandHeight l x = -hostRadius l (seamHeight x) := by
  rw [bandHeight, smoothSign_of_le hx, neg_one_mul]

theorem isLocalDiffeomorphAt_bandHeight (l : ℕ) {x : ℝ} (hx : |x| < 1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (bandHeight l) x := by
  have hD := (bandHeightDeriv_pos l hx).ne'
  let A : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hD)
  have hU : IsOpen {y : ℝ | |y| < 1} := isOpen_lt continuous_abs continuous_const
  refine isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    (bandHeight l) (U := {y : ℝ | |y| < 1}) ?_ hU x hx A ?_
  · intro y hy
    exact (contDiffAt_bandHeight l hy).contMDiffAt.contMDiffWithinAt
  · have h := (hasDerivAt_bandHeight l hx).hasFDerivAt.hasMFDerivAt
    refine h.congr_mfderiv ?_
    ext
    simp [A, ContinuousLinearEquiv.unitsEquivAut_apply]

def tubeSlope : ℝ := 1 / 1000

def angleScale (h : ℝ) : ℝ := Real.sqrt (1 + (tubeSlope * h) ^ 2)

theorem angleScale_pos (h : ℝ) : 0 < angleScale h :=
  Real.sqrt_pos.mpr (by positivity)

theorem angleScale_sq (h : ℝ) : angleScale h ^ 2 = 1 + (tubeSlope * h) ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem one_le_angleScale (h : ℝ) : 1 ≤ angleScale h := by
  rw [angleScale, Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [sq_nonneg (tubeSlope * h)]

theorem angleScale_le (h : ℝ) : angleScale h ≤ 1 + (tubeSlope * h) ^ 2 := by
  rw [angleScale, Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (tubeSlope * h)]

theorem abs_tubeSlope_mul_lt {h : ℝ} (hh : |h| < 3) : |tubeSlope * h| < 3 / 1000 := by
  rw [abs_mul, tubeSlope, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 1000)]
  linarith

def hostTheta (h : ℝ) : ℝ := Real.pi / 2 + Real.arctan (tubeSlope * h)

theorem cos_hostTheta (h : ℝ) : Real.cos (hostTheta h) = -(tubeSlope * h) / angleScale h := by
  rw [hostTheta, add_comm, Real.cos_add_pi_div_two, Real.sin_arctan, angleScale, neg_div]

theorem sin_hostTheta (h : ℝ) : Real.sin (hostTheta h) = 1 / angleScale h := by
  rw [hostTheta, add_comm, Real.sin_add_pi_div_two, Real.cos_arctan, angleScale]

theorem exp_hostTheta (h : ℝ) :
    Complex.exp ((hostTheta h : ℂ) * Complex.I) =
      (⟨-(tubeSlope * h) / angleScale h, 1 / angleScale h⟩ : ℂ) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_hostTheta,
    sin_hostTheta]
  apply Complex.ext <;> simp

theorem exp_neg_hostTheta (h : ℝ) :
    Complex.exp ((-hostTheta h : ℝ) * Complex.I) =
      (⟨-(tubeSlope * h) / angleScale h, -(1 / angleScale h)⟩ : ℂ) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg, cos_hostTheta, sin_hostTheta]
  apply Complex.ext <;> simp

def stripBump (Y : ℝ) : ℝ := 1 - Real.smoothTransition ((4 * Y ^ 2 - 1) / 3)

def stripWidth (Y : ℝ) : ℝ := Real.sqrt (Y ^ 2 + stripBump Y)

theorem stripBump_nonneg (Y : ℝ) : 0 ≤ stripBump Y := by
  have := Real.smoothTransition.le_one ((4 * Y ^ 2 - 1) / 3)
  unfold stripBump
  linarith

theorem stripBump_le_one (Y : ℝ) : stripBump Y ≤ 1 := by
  have := Real.smoothTransition.nonneg ((4 * Y ^ 2 - 1) / 3)
  unfold stripBump
  linarith

theorem stripBump_of_one_le {Y : ℝ} (hY : 1 ≤ |Y|) : stripBump Y = 0 := by
  have h : 1 ≤ (4 * Y ^ 2 - 1) / 3 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [sq_abs Y, abs_nonneg Y]
  rw [stripBump, Real.smoothTransition.one_of_one_le h, sub_self]

theorem stripBump_of_le_half {Y : ℝ} (hY : |Y| ≤ 1 / 2) : stripBump Y = 1 := by
  have h : (4 * Y ^ 2 - 1) / 3 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    nlinarith [sq_abs Y, abs_nonneg Y]
  rw [stripBump, Real.smoothTransition.zero_of_nonpos h, sub_zero]

theorem contDiff_stripBump : ContDiff ℝ ∞ stripBump :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul (contDiff_id.pow 2)).sub contDiff_const).div_const 3))

theorem stripWidth_sq_pos (Y : ℝ) : 0 < Y ^ 2 + stripBump Y := by
  by_cases hY : |Y| ≤ 1 / 2
  · rw [stripBump_of_le_half hY]
    positivity
  · push Not at hY
    have : 0 < Y ^ 2 := by
      rw [← sq_abs]
      nlinarith
    linarith [stripBump_nonneg Y]

theorem stripWidth_pos (Y : ℝ) : 0 < stripWidth Y :=
  Real.sqrt_pos.mpr (stripWidth_sq_pos Y)

theorem stripWidth_of_one_le {Y : ℝ} (hY : 1 ≤ |Y|) : stripWidth Y = |Y| := by
  rw [stripWidth, stripBump_of_one_le hY, add_zero, Real.sqrt_sq_eq_abs]

theorem stripWidth_le (Y : ℝ) : stripWidth Y ≤ |Y| + 1 := by
  rw [stripWidth, Real.sqrt_le_left (by positivity)]
  nlinarith [stripBump_le_one Y, abs_nonneg Y, sq_abs Y]

theorem contDiff_stripWidth : ContDiff ℝ ∞ stripWidth := by
  rw [contDiff_iff_contDiffAt]
  intro Y
  exact ((contDiffAt_id.pow 2).add contDiff_stripBump.contDiffAt).sqrt
    (stripWidth_sq_pos Y).ne'

def stripCenter (l : Fin 3) : ℝ := if l.val = 1 then -(1 / 4) else if l.val = 2 then 1 / 4 else 0

def strip (l : Fin 3) (q : ℝ × ℝ) : ℂ :=
  ⟨-(tubeSlope * q.2) * stripWidth q.1 + stripCenter l * stripBump q.1, q.1⟩

theorem strip_top (l : Fin 3) {R h : ℝ} (hR : angleScale h ≤ R) :
    strip l (R / angleScale h, h) = (R : ℂ) * Complex.exp ((hostTheta h : ℂ) * Complex.I) := by
  have hs := angleScale_pos h
  have hY : 1 ≤ |R / angleScale h| := by
    rw [abs_of_nonneg (div_nonneg (by linarith) hs.le), le_div_iff₀ hs]
    linarith
  rw [exp_hostTheta]
  apply Complex.ext
  · simp only [strip, stripWidth_of_one_le hY, stripBump_of_one_le hY, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [abs_of_nonneg (div_nonneg (by linarith) hs.le)]
    ring
  · simp only [strip, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

theorem strip_bot (l : Fin 3) {R h : ℝ} (hR : angleScale h ≤ R) :
    strip l (-(R / angleScale h), h) =
      (R : ℂ) * Complex.exp ((-hostTheta h : ℝ) * Complex.I) := by
  have hs := angleScale_pos h
  have hY : 1 ≤ |-(R / angleScale h)| := by
    rw [abs_neg, abs_of_nonneg (div_nonneg (by linarith) hs.le), le_div_iff₀ hs]
    linarith
  rw [exp_neg_hostTheta]
  apply Complex.ext
  · simp only [strip, stripWidth_of_one_le hY, stripBump_of_one_le hY, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [abs_neg, abs_of_nonneg (div_nonneg (by linarith) hs.le)]
    ring
  · simp only [strip, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

def hostChart (l : Fin 3) (w : ℂ) : ℂ :=
  if l.val = 0 then w else (planarCenter 3 l : ℂ) + w⁻¹

theorem hostChart_collar (l : Fin 3) (t : Circle) {r : ℝ} (hr : -2 < r) :
    hostChart l ((hostRadius l.val r : ℂ) * t) = planarCollarFormula 3 l ((t : ℂ), r) := by
  unfold hostChart hostRadius planarCollarFormula
  by_cases hl : l.val = 0
  · simp only [hl, ↓reduceIte, planarCenter_zero hl, Complex.ofReal_zero, zero_add,
      planarRadius, planarSign, planarTwist, Complex.real_smul]
    push_cast
    ring
  · have h2 : (2 : ℂ) + r ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have ht : (t : ℂ) ≠ 0 := Circle.coe_ne_zero t
    simp only [hl, ↓reduceIte, planarRadius, planarSign, planarTwist, Complex.real_smul]
    rw [← Circle.coe_inv_eq_conj]
    push_cast
    field_simp
    ring

def pantsInterior : Set ℂ :=
  {z | ‖z‖ < 3 ∧ 1 / 2 < ‖z - ((3 / 2 : ℝ) : ℂ)‖ ∧ 1 / 2 < ‖z + ((3 / 2 : ℝ) : ℂ)‖}

theorem isOpen_pantsInterior : IsOpen pantsInterior :=
  (isOpen_lt continuous_norm continuous_const).inter
    ((isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).inter
      (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.add continuous_const))))

theorem pantsInterior_subset : pantsInterior ⊆ planarModel 3 := by
  intro z hz
  refine ⟨hz.1.le, fun j hj => ?_⟩
  fin_cases j
  · exact absurd rfl hj
  · simpa [planarCenter] using hz.2.1.le
  · have h := hz.2.2.le
    simp only [planarCenter]
    norm_num
    simpa using h

theorem abs_bandHeight_lt (l : ℕ) {x : ℝ} (hx : |x| < 1) (hr : 0 < seamHeight x) :
    |bandHeight l x| < hostRadius l 0 := by
  have hR := hostRadius_pos l (seamHeight_gt hx) (by linarith [seamHeight_le x])
  have hlt : hostRadius l (seamHeight x) < hostRadius l 0 := by
    unfold hostRadius
    split_ifs
    · linarith
    · rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
      linarith
  rw [bandHeight, abs_mul, abs_of_pos hR]
  calc |smoothSign x| * hostRadius l (seamHeight x) ≤ 1 * hostRadius l (seamHeight x) :=
        mul_le_mul_of_nonneg_right (abs_smoothSign_le x) hR.le
    _ < hostRadius l 0 := by rw [one_mul]; exact hlt

theorem normSq_strip (l : Fin 3) (q : ℝ × ℝ) :
    ‖strip l q‖ ^ 2 = (strip l q).re ^ 2 + q.2 ^ 0 * q.1 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [strip]
  ring

theorem strip_re_far (l : Fin 3) {Y h : ℝ} (hY : 1 ≤ |Y|) :
    (strip l (Y, h)).re = -(tubeSlope * h) * |Y| := by
  simp [strip, stripWidth_of_one_le hY, stripBump_of_one_le hY]

theorem strip_re_near (l : Fin 3) {Y h : ℝ} (hY : |Y| ≤ 1 / 2) :
    (strip l (Y, h)).re = -(tubeSlope * h) * stripWidth Y + stripCenter l := by
  simp [strip, stripBump_of_le_half hY]

theorem abs_strip_re_sub_le (l : Fin 3) (Y h : ℝ) :
    |(strip l (Y, h)).re - stripCenter l * stripBump Y| ≤ |tubeSlope * h| * (|Y| + 1) := by
  have : (strip l (Y, h)).re - stripCenter l * stripBump Y = -(tubeSlope * h) * stripWidth Y := by
    simp [strip]
  rw [this, abs_mul, abs_neg, abs_of_pos (stripWidth_pos Y)]
  exact mul_le_mul_of_nonneg_left (stripWidth_le Y) (abs_nonneg _)

theorem norm_sq_strip_far (l : Fin 3) {Y h : ℝ} (hY : 1 ≤ |Y|) :
    ‖strip l (Y, h)‖ ^ 2 = (Y * angleScale h) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, angleScale_sq]
  have hre := strip_re_far l (h := h) hY
  have him : (strip l (Y, h)).im = Y := rfl
  rw [hre, him]
  nlinarith [sq_abs Y]

private theorem hole_ineqs {Y A b : ℝ} (hA : |A| < 3 / 1000)
    (hnear : |Y| ≤ 1 / 2 → b + 1 / 4 ≤ |A| * (3 / 2) ∧ -(b + 1 / 4) ≤ |A| * (3 / 2))
    (hmid : 1 / 2 < |Y| → b ≤ |A| * 2) :
    0 < 27 * b ^ 2 - 12 * b - 4 + 27 * Y ^ 2 ∧ 0 < 35 * b ^ 2 + 24 * b + 4 + 35 * Y ^ 2 := by
  have hA0 := abs_nonneg A
  by_cases hY : |Y| ≤ 1 / 2
  · obtain ⟨h1, h2⟩ := hnear hY
    have hb1 : b ≤ -(1 / 4) + 9 / 2000 := by linarith
    have hb2 : -(1 / 4) - 9 / 2000 ≤ b := by linarith
    constructor
    · nlinarith [sq_nonneg Y]
    · have e : 35 * b ^ 2 + 24 * b + 4 = 35 * (b + 2 / 5) * (b + 2 / 7) := by ring
      have : 0 < 35 * (b + 2 / 5) * (b + 2 / 7) := by
        have : 0 < b + 2 / 7 := by linarith
        have : 0 < b + 2 / 5 := by linarith
        positivity
      nlinarith [sq_nonneg Y]
  · push Not at hY
    have hbm := hmid hY
    have hY' : 1 / 4 < Y ^ 2 := by
      rw [← sq_abs]
      nlinarith
    constructor
    · nlinarith [sq_nonneg b]
    · nlinarith [sq_nonneg (b + 12 / 35)]

private theorem hole_norms {σ a Y : ℝ} (hσ : σ = 1 ∨ σ = -1) (hY2 : a ^ 2 + Y ^ 2 < 4)
    (hI2 : 0 < 27 * (σ * a) ^ 2 - 12 * (σ * a) - 4 + 27 * Y ^ 2)
    (hI3 : 0 < 35 * (σ * a) ^ 2 + 24 * (σ * a) + 4 + 35 * Y ^ 2) :
    (σ * (3 / 2) * a + 1) ^ 2 + (σ * (3 / 2)) ^ 2 * Y ^ 2 < 3 ^ 2 * (a ^ 2 + Y ^ 2) ∧
    (1 / 2) ^ 2 * (a ^ 2 + Y ^ 2) <
      ((σ - 1) * (3 / 2) * a + 1) ^ 2 + ((σ - 1) * (3 / 2)) ^ 2 * Y ^ 2 ∧
    (1 / 2) ^ 2 * (a ^ 2 + Y ^ 2) <
      ((σ + 1) * (3 / 2) * a + 1) ^ 2 + ((σ + 1) * (3 / 2)) ^ 2 * Y ^ 2 := by
  rcases hσ with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem hostChart_strip_mem (l : Fin 3) {x h : ℝ} (hx : |x| < 1) (hr : 0 < seamHeight x)
    (hh : |h| < 3) :
    hostChart l (strip l (bandHeight l.val x / angleScale h, h)) ∈ pantsInterior ∧
      (l.val ≠ 0 → strip l (bandHeight l.val x / angleScale h, h) ≠ 0) := by
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = bandHeight l.val x / angleScale h := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A, A = tubeSlope * h := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = strip l (Y, h) := ⟨_, rfl⟩
  rw [← hYdef, ← hw]
  have hA : |A| < 3 / 1000 := hAdef ▸ abs_tubeSlope_mul_lt hh
  have hs := angleScale_pos h
  have hs1 := one_le_angleScale h
  have hband := abs_bandHeight_lt l.val hx hr
  have hYle : |Y| ≤ |bandHeight l.val x| := by
    rw [hYdef, abs_div, abs_of_pos hs]
    exact div_le_self (abs_nonneg _) hs1
  have him : w.im = Y := by rw [hw]; rfl
  have hn : ‖w‖ ^ 2 = w.re ^ 2 + Y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, him]
    ring
  have hfar : 1 ≤ |Y| → ‖w‖ ^ 2 = bandHeight l.val x ^ 2 := by
    intro h1
    rw [hw, norm_sq_strip_far l h1, hYdef, div_mul_cancel₀ _ hs.ne']
  have hre := abs_strip_re_sub_le l Y h
  rw [← hw, ← hAdef] at hre
  have hβ0 := stripBump_nonneg Y
  have hβ1 := stripBump_le_one Y
  have hA0 := abs_nonneg A
  have hY3 : |Y| < 3 := by
    have : hostRadius l.val 0 ≤ 3 := by
      unfold hostRadius
      split_ifs <;> norm_num
    linarith
  by_cases hl0 : l.val = 0
  · have hc : stripCenter l = 0 := by simp [stripCenter, hl0]
    rw [hc, zero_mul, sub_zero] at hre
    have hR : hostRadius l.val 0 = 3 := by simp [hostRadius, hl0]
    rw [hR] at hband
    have hwre : |w.re| ≤ 3 / 250 := by
      calc |w.re| ≤ |A| * (|Y| + 1) := hre
        _ ≤ 3 / 1000 * 4 := by
          apply mul_le_mul hA.le (by linarith) (by positivity) (by norm_num)
        _ = 3 / 250 := by norm_num
    have hwre' := abs_le.mp hwre
    have hz : hostChart l w = w := by simp [hostChart, hl0]
    rw [hz]
    have hnorm : ‖w‖ < 3 := by
      have : ‖w‖ ^ 2 < 9 := by
        by_cases h1 : 1 ≤ |Y|
        · rw [hfar h1, ← sq_abs]
          nlinarith [abs_nonneg (bandHeight l.val x)]
        · push Not at h1
          rw [hn]
          nlinarith [sq_abs Y, abs_nonneg Y]
      nlinarith [norm_nonneg w]
    have hsub : ∀ c : ℝ, |c| = 3 / 2 → 1 / 2 < ‖w - (c : ℂ)‖ := by
      intro c hc
      have h2 : ‖w - (c : ℂ)‖ ^ 2 = (w.re - c) ^ 2 + Y ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
          sub_zero, him]
        ring
      have h3 : (1 / 2) ^ 2 < ‖w - (c : ℂ)‖ ^ 2 := by
        rw [h2]
        rcases abs_eq (by norm_num : (0 : ℝ) ≤ 3 / 2) |>.mp hc with hc' | hc' <;>
          rw [hc'] <;> nlinarith [sq_nonneg Y]
      nlinarith [norm_nonneg (w - (c : ℂ))]
    refine ⟨⟨hnorm, hsub (3 / 2) (by norm_num), ?_⟩, fun h => absurd hl0 h⟩
    have := hsub (-(3 / 2)) (by norm_num)
    simpa [sub_neg_eq_add] using this
  · have hR : hostRadius l.val 0 = 2 := by simp [hostRadius, hl0]; norm_num
    rw [hR] at hband
    have hl12 : l.val = 1 ∨ l.val = 2 := by omega
    obtain ⟨σ, hσ2, hcen, hpc⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ stripCenter l = -(σ / 4) ∧
        (planarCenter 3 l : ℂ) = ((σ * (3 / 2) : ℝ) : ℂ) := by
      rcases hl12 with h1 | h2
      · exact ⟨1, Or.inl rfl, by simp [stripCenter, h1], by simp [planarCenter, h1]⟩
      · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
        · simp [stripCenter, h2]
          norm_num
        · simp [planarCenter, h2]
    obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = σ * w.re := ⟨_, rfl⟩
    have hY2 : w.re ^ 2 + Y ^ 2 < 4 := by
      by_cases h1 : 1 ≤ |Y|
      · rw [← hn, hfar h1, ← sq_abs]
        nlinarith [abs_nonneg (bandHeight l.val x)]
      · push Not at h1
        have h4 : |stripCenter l * stripBump Y| ≤ 1 / 4 := by
          rw [hcen, abs_mul, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
            abs_of_nonneg hβ0]
          rcases hσ2 with hσ1 | hσ1 <;> rw [hσ1] <;> norm_num <;> linarith
        have h5 : |A| * (|Y| + 1) ≤ 3 / 1000 * 2 :=
          mul_le_mul hA.le (by linarith) (by positivity) (by norm_num)
        have h6 : |w.re| ≤ 1 / 4 + 3 / 1000 * 2 := by
          have h7 := abs_add_le (w.re - stripCenter l * stripBump Y)
            (stripCenter l * stripBump Y)
          rw [sub_add_cancel] at h7
          linarith
        nlinarith [sq_abs w.re, abs_nonneg w.re, sq_abs Y, abs_nonneg Y]
    have hnear : |Y| ≤ 1 / 2 → b + 1 / 4 ≤ |A| * (3 / 2) ∧ -(b + 1 / 4) ≤ |A| * (3 / 2) := by
      intro h1
      have e := strip_re_near l (h := h) h1
      rw [← hw, hcen, ← hAdef] at e
      have hW := stripWidth_le Y
      have hWp := stripWidth_pos Y
      have habs : |A * stripWidth Y| ≤ |A| * (3 / 2) := by
        rw [abs_mul, abs_of_pos hWp]
        exact mul_le_mul_of_nonneg_left (by linarith) hA0
      have habs' := abs_le.mp habs
      rw [hbdef, e]
      rcases hσ2 with hσ1 | hσ1 <;> rw [hσ1] <;> constructor <;> linarith [habs'.1, habs'.2]
    have hmid : 1 / 2 < |Y| → b ≤ |A| * 2 := by
      intro h1
      have hre' := abs_le.mp hre
      have hcb : σ * (stripCenter l * stripBump Y) ≤ 0 := by
        rw [hcen]
        rcases hσ2 with hσ1 | hσ1 <;> rw [hσ1] <;> linarith
      have hsplit : b = σ * (w.re - stripCenter l * stripBump Y) +
          σ * (stripCenter l * stripBump Y) := by
        rw [hbdef]
        ring
      have hA2 : |A| * (|Y| + 1) ≤ |A| * 4 := mul_le_mul_of_nonneg_left (by linarith) hA0
      by_cases h2 : 1 ≤ |Y|
      · have e := strip_re_far l (h := h) h2
        rw [← hw, ← hAdef] at e
        have hc0 : stripBump Y = 0 := stripBump_of_one_le h2
        have hyb : |Y| < 2 := by linarith
        rw [hbdef, e]
        have hAY : abs (A * |Y|) ≤ |A| * 2 := by
          rw [abs_mul, abs_abs]
          exact mul_le_mul_of_nonneg_left hyb.le hA0
        have hAY' := abs_le.mp hAY
        rcases hσ2 with hσ1 | hσ1 <;> rw [hσ1] <;> linarith [hAY'.1, hAY'.2]
      · push Not at h2
        have hA3 : |A| * (|Y| + 1) ≤ |A| * 2 := mul_le_mul_of_nonneg_left (by linarith) hA0
        have : σ * (w.re - stripCenter l * stripBump Y) ≤ |A| * 2 := by
          rcases hσ2 with hσ1 | hσ1 <;> rw [hσ1] <;> linarith
        linarith
    obtain ⟨hI2, hI3⟩ := hole_ineqs hA hnear hmid
    rw [hbdef] at hI2 hI3
    obtain ⟨hP1, hP2, hP3⟩ := hole_norms hσ2 hY2 hI2 hI3
    have hw0 : w ≠ 0 := by
      intro h0
      have hre0 : w.re = 0 := by rw [h0]; rfl
      have hY0 : Y = 0 := by rw [← him, h0]; rfl
      rw [hre0, hY0] at hY2 hI2
      norm_num at hI2
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hz : hostChart l w = ((σ * (3 / 2) : ℝ) : ℂ) + w⁻¹ := by
      simp [hostChart, hl0, hpc]
    rw [hz]
    have key : ∀ c : ℂ, ‖c + w⁻¹‖ = ‖c * w + 1‖ / ‖w‖ := by
      intro c
      rw [eq_div_iff hwn.ne', ← norm_mul, add_mul, inv_mul_cancel₀ hw0]
    have hnsq : ∀ p : ℝ, ‖((p : ℝ) : ℂ) * w + 1‖ ^ 2 = (p * w.re + 1) ^ 2 + p ^ 2 * Y ^ 2 := by
      intro p
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_im, Complex.mul_im, Complex.one_re, Complex.one_im, him]
      ring
    have hlt : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → p ^ 2 < q ^ 2 → p < q := fun hp hq h =>
      lt_of_pow_lt_pow_left₀ 2 hq h
    refine ⟨⟨?_, ?_, ?_⟩, fun _ => hw0⟩
    · rw [key, div_lt_iff₀ hwn]
      refine hlt (norm_nonneg _) (by positivity) ?_
      rw [hnsq, show (3 * ‖w‖) ^ 2 = 3 ^ 2 * ‖w‖ ^ 2 from mul_pow _ _ _, hn]
      exact hP1
    · have e1 : ((σ * (3 / 2) : ℝ) : ℂ) + w⁻¹ - ((3 / 2 : ℝ) : ℂ) =
          (((σ - 1) * (3 / 2) : ℝ) : ℂ) + w⁻¹ := by push_cast; ring
      rw [e1, key, lt_div_iff₀ hwn]
      refine hlt (by positivity) (norm_nonneg _) ?_
      rw [hnsq, show (1 / 2 * ‖w‖) ^ 2 = (1 / 2) ^ 2 * ‖w‖ ^ 2 from mul_pow _ _ _, hn]
      exact hP2
    · have e1 : ((σ * (3 / 2) : ℝ) : ℂ) + w⁻¹ + ((3 / 2 : ℝ) : ℂ) =
          (((σ + 1) * (3 / 2) : ℝ) : ℂ) + w⁻¹ := by push_cast; ring
      rw [e1, key, lt_div_iff₀ hwn]
      refine hlt (by positivity) (norm_nonneg _) ?_
      rw [hnsq, show (1 / 2 * ‖w‖) ^ 2 = (1 / 2) ^ 2 * ‖w‖ ^ 2 from mul_pow _ _ _, hn]
      exact hP3

end GC.Seifert.SplitTube
