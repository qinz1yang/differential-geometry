import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypRadii
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldBridge

/-!
# Profile and bridges of the hyperbolic compact fold

Lane CF-H, tier 2 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`, §3, curvature `-1`).
The moduli are linear in the canonical coordinates `canon j = tanh ((dⱼ - rⱼ)/2)` with the slope
`compactProfileSlope = 2/5`: `modOne = 3/2 + κ canon 0`, `modTwo = 3/2 + κ canon 1`,
`modThree = 3 - κ canon 2`. Since `|canon j| < 1` on the whole disc, `modOne, modTwo ∈ (11/10,
19/10)` and `modThree ∈ (13/5, 17/5)` there (`modOne_mem`, …).

The bridges are A4's `twoCircle` with the cofactors of `CompactFoldHypRadii`: `bridgeOne` (wall 1,
side function `wallSide 1`), `bridgeZero` (wall 0, `wallSide 0`) and `bridgeTwo` (wall 2, side
coordinate `sideTwo = Im rotTwo`, a positive multiple of `wallSide 2`). The cofactor domains
`domOneThree`, `domZeroThree`, `domOneTwo` are open (`isOpen_pairDom`), contain the triangle minus
the two vertices of the wall (`mem_dom*` of `CompactFoldHypRadii`), and on them each bridge is
smooth (`contDiffAt_bridge*`, via `contDiffAt_pairCof`), lies on its two circles
(`norm_bridge*`) and has the sign of its side function as the sign of its imaginary part.
Reflection invariance of the pseudo-hyperbolic distances (`hd_refl_*`) and of the cofactors
(`pairCof_conj`) gives the wall identities `bridge ∘ refl = conj ∘ bridge`. On the disc
`Re bridgeOne > 0`, `Re bridgeZero < 0`, and on the domains `‖bridgeTwo‖ < 3/2`,
`‖bridgeOne‖, ‖bridgeZero‖ > 13/5`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace HypFold

theorem isOpen_pairDom {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : IsOpen (pairDom t) := by
  rw [isOpen_iff_mem_nhds]
  intro W hW
  obtain ⟨hW1, h1, h2⟩ := hW
  have hne : 1 - conj (t : ℂ) * W ≠ 0 := by
    rw [Complex.conj_ofReal]
    exact one_sub_ofReal_mul_ne_zero ht0 ht1 hW1
  have cm : ContinuousAt (fun u : ℂ => ‖mob (t : ℂ) u‖) W :=
    (contDiffAt_mob hne).continuousAt.norm
  have c1 : ContinuousAt (fun u : ℂ => ‖u‖) W := continuous_norm.continuousAt
  have c2 : ContinuousAt (fun u : ℂ => ‖u‖ + u.re) W :=
    (continuous_norm.add Complex.continuous_re).continuousAt
  have c3 : ContinuousAt (fun u : ℂ => ‖mob (t : ℂ) u‖ * (1 - t * u.re) + t - u.re) W :=
    ((cm.mul (continuous_const.sub (continuous_const.mul
      Complex.continuous_re)).continuousAt).add continuousAt_const).sub
      Complex.continuous_re.continuousAt
  filter_upwards [c1.eventually_lt continuousAt_const hW1,
    continuousAt_const.eventually_lt c2 h1, continuousAt_const.eventually_lt c3 h2]
    with u a b c
  exact ⟨a, b, c⟩

theorem ne_zero_of_mem_pairDom {t : ℝ} {W : ℂ} (hW : W ∈ pairDom t) : W ≠ 0 := by
  rintro rfl
  have := hW.2.1
  simp at this

theorem mob_ne_zero_of_mem_pairDom {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {W : ℂ}
    (hW : W ∈ pairDom t) : mob (t : ℂ) W ≠ 0 := by
  intro h0
  have h2 := hW.2.2
  have hW0 : W = (t : ℂ) := by
    rw [mob, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact sub_eq_zero.1 h0
    · rw [Complex.conj_ofReal] at h0
      exact absurd h0 (one_sub_ofReal_mul_ne_zero ht0 ht1 hW.1)
  rw [h0, norm_zero, zero_mul, zero_add, hW0, ofReal_re, sub_self] at h2
  exact lt_irrefl _ h2

theorem contDiffAt_pairCof {t a b : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) {W : ℂ} (hW : W ∈ pairDom t) :
    ContDiffAt ℝ ∞ (pairCof t a b) W := by
  have hW0 := ne_zero_of_mem_pairDom hW
  have hm0 := mob_ne_zero_of_mem_pairDom ht0 ht1 hW
  obtain ⟨hW1, h1, h2⟩ := hW
  have hne : 1 - conj (t : ℂ) * W ≠ 0 := by
    rw [Complex.conj_ofReal]
    exact one_sub_ofReal_mul_ne_zero ht0 ht1 hW1
  have hm1 := norm_mob_ofReal_lt_one ht0 ht1 hW1
  have hX1 : W.re < 1 := lt_of_le_of_lt (Complex.re_le_norm W) hW1
  have hD : 0 < 1 - t * W.re := by nlinarith
  have hN : 0 < (1 - t * W.re) ^ 2 + t ^ 2 * W.im ^ 2 := by positivity
  have hr : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) W := contDiffAt_norm ℝ hW0
  have hm : ContDiffAt ℝ ∞ (fun u : ℂ => ‖mob (t : ℂ) u‖) W := (contDiffAt_mob hne).norm ℝ hm0
  have hX : ContDiffAt ℝ ∞ (fun u : ℂ => u.re) W := reCLM.contDiff.contDiffAt
  have hY : ContDiffAt ℝ ∞ (fun u : ℂ => u.im) W := imCLM.contDiff.contDiffAt
  have hB : ContDiffAt ℝ ∞ (fun u : ℂ => bracketCof t u.re u.im ‖u‖ ‖mob (t : ℂ) u‖) W := by
    unfold bracketCof
    refine ((contDiffAt_const.sub (contDiffAt_const.mul hm)).div (hr.add hX) h1.ne').add
      ((contDiffAt_const.mul ((contDiffAt_const.sub (contDiffAt_const.mul hX)).add
        contDiffAt_const)).div ((((contDiffAt_const.sub (contDiffAt_const.mul hX)).pow 2).add
        (contDiffAt_const.mul (hY.pow 2))).mul
        (((hm.mul (contDiffAt_const.sub (contDiffAt_const.mul hX))).add contDiffAt_const).sub
          hX)) (mul_pos hN h2).ne')
  have e1 : 0 < 1 - ‖W‖ * a := by nlinarith [norm_nonneg W]
  have e2 : 0 < 1 - ‖mob (t : ℂ) W‖ * b := by nlinarith [norm_nonneg (mob (t : ℂ) W)]
  have hF : ContDiffAt ℝ ∞
      (fun u : ℂ => (1 + a * b) / ((1 - ‖u‖ * a) * (1 - ‖mob (t : ℂ) u‖ * b))) W :=
    contDiffAt_const.div ((contDiffAt_const.sub (hr.mul contDiffAt_const)).mul
      (contDiffAt_const.sub (hm.mul contDiffAt_const))) (mul_pos e1 e2).ne'
  exact hF.mul hB

theorem pairCof_conj {t a b : ℝ} (W : ℂ) : pairCof t a b (conj W) = pairCof t a b W := by
  unfold pairCof bracketCof
  rw [norm_mob_conj_ofReal, Complex.norm_conj, Complex.conj_re, Complex.conj_im, neg_sq]

variable (σ : CompactShape)

def modOne (z : ℂ) : ℝ := 3 / 2 + compactProfileSlope * canon σ 0 z

def modTwo (z : ℂ) : ℝ := 3 / 2 + compactProfileSlope * canon σ 1 z

def modThree (z : ℂ) : ℝ := 3 - compactProfileSlope * canon σ 2 z

def sideTwo (z : ℂ) : ℝ := (σ.rotTwo z).im

def cofTwo (z : ℂ) : ℝ := pairCof (sideOneTwo σ) (tauTwo σ) (tauOne σ) (σ.rotTwo z)

def cofBridgeOne (z : ℂ) : ℝ :=
  ((modThree σ z + modOne σ z) ^ 2 - 9 / 4) * (3 / 2 + modThree σ z - modOne σ z) *
    (compactProfileSlope * cofOneThree σ z)

def cofBridgeZero (z : ℂ) : ℝ :=
  ((modThree σ z + modTwo σ z) ^ 2 - 9 / 4) * (3 / 2 + modThree σ z - modTwo σ z) *
    (compactProfileSlope * cofZeroThree σ z)

def cofBridgeTwo (z : ℂ) : ℝ :=
  (modOne σ z + modTwo σ z + 3) * (9 - (modOne σ z - modTwo σ z) ^ 2) *
    (compactProfileSlope * cofTwo σ z)

def bridgeOne (z : ℂ) : ℂ :=
  twoCircle 0 (3 / 2) (modThree σ z) (modOne σ z) (σ.wallSide 1 z) (cofBridgeOne σ z)

def bridgeZero (z : ℂ) : ℂ :=
  twoCircle 0 (-(3 / 2)) (modThree σ z) (modTwo σ z) (σ.wallSide 0 z) (cofBridgeZero σ z)

def bridgeTwo (z : ℂ) : ℂ :=
  twoCircle (3 / 2) (-(3 / 2)) (modOne σ z) (modTwo σ z) (sideTwo σ z) (cofBridgeTwo σ z)

variable {σ}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem modOne_mem {z : ℂ} (hz : ‖z‖ < 1) : 11 / 10 < modOne σ z ∧ modOne σ z < 19 / 10 := by
  have := abs_lt.1 (abs_canon_lt_one h 0 hz)
  unfold modOne compactProfileSlope
  constructor <;> linarith [this.1, this.2]

theorem modTwo_mem {z : ℂ} (hz : ‖z‖ < 1) : 11 / 10 < modTwo σ z ∧ modTwo σ z < 19 / 10 := by
  have := abs_lt.1 (abs_canon_lt_one h 1 hz)
  unfold modTwo compactProfileSlope
  constructor <;> linarith [this.1, this.2]

theorem modThree_mem {z : ℂ} (hz : ‖z‖ < 1) :
    13 / 5 < modThree σ z ∧ modThree σ z < 17 / 5 := by
  have := abs_lt.1 (abs_canon_lt_one h 2 hz)
  unfold modThree compactProfileSlope
  constructor <;> linarith [this.1, this.2]

omit h in
theorem norm_lt_one_of_domZeroThree {z : ℂ} (hz : z ∈ domZeroThree σ) : ‖z‖ < 1 := hz.1

omit h in
theorem norm_exp_neg_mul (z : ℂ) : ‖exp (-((σ.θ₃ : ℂ) * I)) * z‖ = ‖z‖ := by
  rw [norm_mul, show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

omit h in
theorem norm_lt_one_of_domOneThree {z : ℂ} (hz : z ∈ domOneThree σ) : ‖z‖ < 1 := by
  have := hz.1
  rwa [norm_exp_neg_mul] at this

omit h in
theorem norm_lt_one_of_domOneTwo {z : ℂ} (hz : z ∈ domOneTwo σ) : ‖z‖ < 1 := hz.1

theorem canon_add_canon_side_two {z : ℂ} (hz : z ∈ domOneTwo σ) :
    canon σ 0 z + canon σ 1 z = sideTwo σ z ^ 2 * cofTwo σ z := by
  have e := pair_bracket (sideOneTwo_pos h) (sideOneTwo_lt_one h) (tauTwo_pos h)
    tauTwo_lt_one (tauOne_pos h) tauOne_lt_one
    (by rw [oplus_comm]; exact oplus_tauOne_tauTwo h) hz.2
  have h1 := norm_disc_vertexOne_eq h hz.1
  rw [CompactShape.disc_eq_mob h] at h1
  rw [norm_rotTwo h, ← h1] at e
  rw [add_comm]
  exact e

theorem cofTwo_pos {z : ℂ} (hz : z ∈ domOneTwo σ) : 0 < cofTwo σ z :=
  pairCof_pos (sideOneTwo_pos h) (sideOneTwo_lt_one h) (tauTwo_pos h) tauTwo_lt_one
    (tauOne_pos h) tauOne_lt_one hz.2

theorem cofBridgeOne_pos {z : ℂ} (hz : z ∈ domOneThree σ) : 0 < cofBridgeOne σ z := by
  have hz1 := norm_lt_one_of_domOneThree hz
  have hc := cofOneThree_pos h hz
  have a := modOne_mem h hz1
  have b := modThree_mem h hz1
  have e1 : 0 < (modThree σ z + modOne σ z) ^ 2 - 9 / 4 := by nlinarith
  have e2 : 0 < 3 / 2 + modThree σ z - modOne σ z := by linarith
  unfold cofBridgeOne compactProfileSlope
  positivity

theorem cofBridgeZero_pos {z : ℂ} (hz : z ∈ domZeroThree σ) : 0 < cofBridgeZero σ z := by
  have hz1 := norm_lt_one_of_domZeroThree hz
  have hc := cofZeroThree_pos h hz
  have a := modTwo_mem h hz1
  have b := modThree_mem h hz1
  have e1 : 0 < (modThree σ z + modTwo σ z) ^ 2 - 9 / 4 := by nlinarith
  have e2 : 0 < 3 / 2 + modThree σ z - modTwo σ z := by linarith
  unfold cofBridgeZero compactProfileSlope
  positivity

theorem cofBridgeTwo_pos {z : ℂ} (hz : z ∈ domOneTwo σ) : 0 < cofBridgeTwo σ z := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have hc := cofTwo_pos h hz
  have a := modOne_mem h hz1
  have b := modTwo_mem h hz1
  have e1 : 0 < modOne σ z + modTwo σ z + 3 := by linarith
  have e2 : 0 < 9 - (modOne σ z - modTwo σ z) ^ 2 := by nlinarith
  unfold cofBridgeTwo compactProfileSlope
  positivity

theorem heron_bridgeOne {z : ℂ} (hz : z ∈ domOneThree σ) :
    ((modThree σ z + modOne σ z) ^ 2 - (3 / 2 - 0) ^ 2) *
        ((3 / 2 - 0) ^ 2 - (modThree σ z - modOne σ z) ^ 2) =
      σ.wallSide 1 z ^ 2 * cofBridgeOne σ z := by
  have hc := canon_add_canon_one_three h hz
  have e : 3 / 2 - modThree σ z + modOne σ z =
      compactProfileSlope * (canon σ 0 z + canon σ 2 z) := by
    unfold modThree modOne
    ring
  rw [hc] at e
  unfold cofBridgeOne
  have : (3 / 2 - 0 : ℝ) ^ 2 - (modThree σ z - modOne σ z) ^ 2 =
      (3 / 2 - modThree σ z + modOne σ z) * (3 / 2 + modThree σ z - modOne σ z) := by ring
  rw [this, e]
  ring

theorem heron_bridgeZero {z : ℂ} (hz : z ∈ domZeroThree σ) :
    ((modThree σ z + modTwo σ z) ^ 2 - (-(3 / 2) - 0) ^ 2) *
        ((-(3 / 2) - 0) ^ 2 - (modThree σ z - modTwo σ z) ^ 2) =
      σ.wallSide 0 z ^ 2 * cofBridgeZero σ z := by
  have hc := canon_add_canon_zero_three h hz
  have e : 3 / 2 - modThree σ z + modTwo σ z =
      compactProfileSlope * (canon σ 1 z + canon σ 2 z) := by
    unfold modThree modTwo
    ring
  rw [hc] at e
  unfold cofBridgeZero
  have : (-(3 / 2) - 0 : ℝ) ^ 2 - (modThree σ z - modTwo σ z) ^ 2 =
      (3 / 2 - modThree σ z + modTwo σ z) * (3 / 2 + modThree σ z - modTwo σ z) := by ring
  rw [this, e]
  ring

theorem heron_bridgeTwo {z : ℂ} (hz : z ∈ domOneTwo σ) :
    ((modOne σ z + modTwo σ z) ^ 2 - (-(3 / 2) - 3 / 2) ^ 2) *
        ((-(3 / 2) - 3 / 2) ^ 2 - (modOne σ z - modTwo σ z) ^ 2) =
      sideTwo σ z ^ 2 * cofBridgeTwo σ z := by
  have hc := canon_add_canon_side_two h hz
  have e : modOne σ z + modTwo σ z - 3 = compactProfileSlope * (canon σ 0 z + canon σ 1 z) := by
    unfold modOne modTwo
    ring
  rw [hc] at e
  unfold cofBridgeTwo
  have : (modOne σ z + modTwo σ z) ^ 2 - (-(3 / 2) - 3 / 2 : ℝ) ^ 2 =
      (modOne σ z + modTwo σ z - 3) * (modOne σ z + modTwo σ z + 3) := by ring
  rw [this, e]
  ring

theorem norm_bridgeOne {z : ℂ} (hz : z ∈ domOneThree σ) :
    ‖bridgeOne σ z‖ = modThree σ z ∧ ‖bridgeOne σ z - 3 / 2‖ = modOne σ z := by
  have hz1 := norm_lt_one_of_domOneThree hz
  have hab : (0 : ℝ) ≠ 3 / 2 := by norm_num
  have hP := (cofBridgeOne_pos h hz).le
  have hH := heron_bridgeOne h hz
  constructor
  · have h' := norm_twoCircle_sub_left hab hP (by linarith [(modThree_mem h hz1).1]) hH
    simpa [bridgeOne] using h'
  · have h' := norm_twoCircle_sub_right hab hP (by linarith [(modOne_mem h hz1).1]) hH
    rw [bridgeOne]
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring] at h'
    exact h'

theorem norm_bridgeZero {z : ℂ} (hz : z ∈ domZeroThree σ) :
    ‖bridgeZero σ z‖ = modThree σ z ∧ ‖bridgeZero σ z + 3 / 2‖ = modTwo σ z := by
  have hz1 := norm_lt_one_of_domZeroThree hz
  have hab : (0 : ℝ) ≠ -(3 / 2) := by norm_num
  have hP := (cofBridgeZero_pos h hz).le
  have hH := heron_bridgeZero h hz
  constructor
  · have h' := norm_twoCircle_sub_left hab hP (by linarith [(modThree_mem h hz1).1]) hH
    simpa [bridgeZero] using h'
  · have h' := norm_twoCircle_sub_right hab hP (by linarith [(modTwo_mem h hz1).1]) hH
    rw [bridgeZero]
    rw [show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add] at h'
    exact h'

theorem norm_bridgeTwo {z : ℂ} (hz : z ∈ domOneTwo σ) :
    ‖bridgeTwo σ z - 3 / 2‖ = modOne σ z ∧ ‖bridgeTwo σ z + 3 / 2‖ = modTwo σ z := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have hab : (3 / 2 : ℝ) ≠ -(3 / 2) := by norm_num
  have hP := (cofBridgeTwo_pos h hz).le
  have hH := heron_bridgeTwo h hz
  constructor
  · have h' := norm_twoCircle_sub_left hab hP (by linarith [(modOne_mem h hz1).1]) hH
    rw [bridgeTwo]
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring] at h'
    exact h'
  · have h' := norm_twoCircle_sub_right hab hP (by linarith [(modTwo_mem h hz1).1]) hH
    rw [bridgeTwo]
    rw [show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add] at h'
    exact h'

theorem im_bridgeOne_pos {z : ℂ} (hz : z ∈ domOneThree σ) (hw : 0 < σ.wallSide 1 z) :
    0 < (bridgeOne σ z).im :=
  twoCircle_im_pos (by norm_num) hw (cofBridgeOne_pos h hz)

theorem im_bridgeZero_pos {z : ℂ} (hz : z ∈ domZeroThree σ) (hw : 0 < σ.wallSide 0 z) :
    0 < (bridgeZero σ z).im :=
  twoCircle_im_pos (by norm_num) hw (cofBridgeZero_pos h hz)

theorem im_bridgeTwo_pos {z : ℂ} (hz : z ∈ domOneTwo σ) (hw : 0 < sideTwo σ z) :
    0 < (bridgeTwo σ z).im :=
  twoCircle_im_pos (by norm_num) hw (cofBridgeTwo_pos h hz)

omit h in
theorem im_bridgeOne_eq_zero {z : ℂ} (hw : σ.wallSide 1 z = 0) : (bridgeOne σ z).im = 0 := by
  rw [bridgeOne, hw, twoCircle_im_eq_zero]

omit h in
theorem im_bridgeZero_eq_zero {z : ℂ} (hw : σ.wallSide 0 z = 0) :
    (bridgeZero σ z).im = 0 := by
  rw [bridgeZero, hw, twoCircle_im_eq_zero]

omit h in
theorem im_bridgeTwo_eq_zero {z : ℂ} (hw : sideTwo σ z = 0) : (bridgeTwo σ z).im = 0 := by
  rw [bridgeTwo, hw, twoCircle_im_eq_zero]

theorem re_bridgeOne_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (bridgeOne σ z).re := by
  have hA := modThree_mem h hz
  have hB := modOne_mem h hz
  rw [bridgeOne, twoCircle_re]
  have : 0 < modThree σ z ^ 2 - modOne σ z ^ 2 + (3 / 2 - 0) ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < 2 * (3 / 2 - 0) := by norm_num
  have := div_pos this h2
  linarith

theorem re_bridgeZero_neg {z : ℂ} (hz : ‖z‖ < 1) : (bridgeZero σ z).re < 0 := by
  have hA := modThree_mem h hz
  have hB := modTwo_mem h hz
  rw [bridgeZero, twoCircle_re]
  have : 0 < modThree σ z ^ 2 - modTwo σ z ^ 2 + (-(3 / 2) - 0) ^ 2 := by nlinarith
  have h2 : 2 * (-(3 / 2) - 0 : ℝ) < 0 := by norm_num
  have := div_neg_of_pos_of_neg this h2
  linarith

theorem norm_bridgeOne_gt {z : ℂ} (hz : z ∈ domOneThree σ) : 13 / 5 < ‖bridgeOne σ z‖ := by
  rw [(norm_bridgeOne h hz).1]
  exact (modThree_mem h (norm_lt_one_of_domOneThree hz)).1

theorem norm_bridgeZero_gt {z : ℂ} (hz : z ∈ domZeroThree σ) : 13 / 5 < ‖bridgeZero σ z‖ := by
  rw [(norm_bridgeZero h hz).1]
  exact (modThree_mem h (norm_lt_one_of_domZeroThree hz)).1

omit h in
theorem normSq_eq_sq_norm_aux (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem norm_bridgeTwo_lt {z : ℂ} (hz : z ∈ domOneTwo σ) : ‖bridgeTwo σ z‖ < 3 / 2 := by
  obtain ⟨e1, e2⟩ := norm_bridgeTwo h hz
  have hA := modOne_mem h (norm_lt_one_of_domOneTwo hz)
  have hB := modTwo_mem h (norm_lt_one_of_domOneTwo hz)
  have q1 := normSq_eq_sq_norm_aux (bridgeTwo σ z - 3 / 2)
  have q2 := normSq_eq_sq_norm_aux (bridgeTwo σ z + 3 / 2)
  have q := normSq_eq_sq_norm_aux (bridgeTwo σ z)
  rw [e1] at q1
  rw [e2] at q2
  simp only [sub_re, add_re, sub_im, add_im, div_ofNat_re, div_ofNat_im, Complex.re_ofNat,
    Complex.im_ofNat, zero_div, sub_zero, add_zero] at q1 q2
  have hsq : ‖bridgeTwo σ z‖ ^ 2 < (3 / 2) ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

theorem hd_refl_zero_one (z : ℂ) : hd σ 1 (σ.refl 0 z) = hd σ 1 z := by
  have e := norm_disc_refl_zero_two h z
  rwa [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h] at e

theorem hd_refl_zero_two (z : ℂ) : hd σ 2 (σ.refl 0 z) = hd σ 2 z := by
  have e := norm_disc_refl_zero_zero h z
  rwa [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h, mob_zero_left,
    mob_zero_left] at e

theorem hd_refl_one_zero (z : ℂ) : hd σ 0 (σ.refl 1 z) = hd σ 0 z := by
  have e := norm_disc_refl_one_one h z
  rwa [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h] at e

theorem hd_refl_one_two (z : ℂ) : hd σ 2 (σ.refl 1 z) = hd σ 2 z := by
  have e := norm_disc_refl_one_zero h z
  rwa [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h, mob_zero_left,
    mob_zero_left] at e

theorem hd_refl_two_zero {z : ℂ} (hz : ‖z‖ < 1) : hd σ 0 (σ.refl 2 z) = hd σ 0 z := by
  have e := norm_disc_refl_two_one h hz
  rwa [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h] at e

theorem hd_refl_two_one {z : ℂ} (hz : ‖z‖ < 1) : hd σ 1 (σ.refl 2 z) = hd σ 1 z := by
  have e := norm_disc_refl_two_two h hz
  rwa [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h] at e

omit h in
theorem canon_eq_of_hd {j : Fin 3} {z w : ℂ} (e : hd σ j w = hd σ j z) :
    canon σ j w = canon σ j z := by
  rw [canon, canon, e]

omit h in
theorem exp_neg_mul_refl_one (z : ℂ) :
    exp (-((σ.θ₃ : ℂ) * I)) * σ.refl 1 z = conj (exp (-((σ.θ₃ : ℂ) * I)) * z) := by
  change exp (-((σ.θ₃ : ℂ) * I)) * (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) = _
  rw [map_mul, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem bridgeOne_refl_one (z : ℂ) : bridgeOne σ (σ.refl 1 z) = conj (bridgeOne σ z) := by
  have h0 := canon_eq_of_hd (hd_refl_one_zero h z)
  have h2 := canon_eq_of_hd (hd_refl_one_two h z)
  have hc : cofOneThree σ (σ.refl 1 z) = cofOneThree σ z := by
    rw [cofOneThree, cofOneThree, exp_neg_mul_refl_one, pairCof_conj]
  have hb : cofBridgeOne σ (σ.refl 1 z) = cofBridgeOne σ z := by
    rw [cofBridgeOne, cofBridgeOne, modThree, modThree, modOne, modOne, h0, h2, hc]
  rw [bridgeOne, bridgeOne, modThree, modThree, modOne, modOne, h0, h2, hb, wallSide_refl_one,
    twoCircle_neg]

theorem bridgeZero_refl_zero (z : ℂ) : bridgeZero σ (σ.refl 0 z) = conj (bridgeZero σ z) := by
  have h1 := canon_eq_of_hd (hd_refl_zero_one h z)
  have h2 := canon_eq_of_hd (hd_refl_zero_two h z)
  have hc : cofZeroThree σ (σ.refl 0 z) = cofZeroThree σ z := by
    rw [cofZeroThree, cofZeroThree]
    exact pairCof_conj z
  have hb : cofBridgeZero σ (σ.refl 0 z) = cofBridgeZero σ z := by
    rw [cofBridgeZero, cofBridgeZero, modThree, modThree, modTwo, modTwo, h1, h2, hc]
  rw [bridgeZero, bridgeZero, modThree, modThree, modTwo, modTwo, h1, h2, hb, wallSide_refl_zero,
    twoCircle_neg]

theorem sideTwo_refl_two {z : ℂ} (hz : ‖z‖ < 1) : sideTwo σ (σ.refl 2 z) = -sideTwo σ z := by
  rw [sideTwo, sideTwo, rotTwo_refl_two h hz, Complex.conj_im]

theorem bridgeTwo_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    bridgeTwo σ (σ.refl 2 z) = conj (bridgeTwo σ z) := by
  have h0 := canon_eq_of_hd (hd_refl_two_zero h hz)
  have h1 := canon_eq_of_hd (hd_refl_two_one h hz)
  have hc : cofTwo σ (σ.refl 2 z) = cofTwo σ z := by
    rw [cofTwo, cofTwo, rotTwo_refl_two h hz, pairCof_conj]
  have hb : cofBridgeTwo σ (σ.refl 2 z) = cofBridgeTwo σ z := by
    rw [cofBridgeTwo, cofBridgeTwo, modOne, modOne, modTwo, modTwo, h0, h1, hc]
  rw [bridgeTwo, bridgeTwo, modOne, modOne, modTwo, modTwo, h0, h1, hb, sideTwo_refl_two h hz,
    twoCircle_neg]

theorem contDiffAt_hd (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) (hne : hd σ j z ≠ 0) :
    ContDiffAt ℝ ∞ (hd σ j) z := by
  fin_cases j
  · exact (contDiffAt_mob (one_sub_conj_mul_ne_zero (norm_vertexOne_lt_one h) hz)).norm ℝ
      (norm_ne_zero_iff.1 hne)
  · exact (contDiffAt_mob (one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz)).norm ℝ
      (norm_ne_zero_iff.1 hne)
  · exact contDiffAt_norm ℝ (norm_ne_zero_iff.1 hne)

theorem contDiffAt_canon (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) (hne : hd σ j z ≠ 0) :
    ContDiffAt ℝ ∞ (canon σ j) z := by
  have hd1 := hd_lt_one h j hz
  have hd0 := hd_nonneg (σ := σ) j z
  obtain ⟨t0, t1⟩ := tau_mem h j
  have hD : 0 < 1 - hd σ j z * tau σ j := by nlinarith
  have hc := contDiffAt_hd h j hz hne
  exact (hc.sub contDiffAt_const).div (contDiffAt_const.sub (hc.mul contDiffAt_const)) hD.ne'

theorem contDiffAt_rotTwo {z : ℂ} (hz : ‖z‖ < 1) : ContDiffAt ℝ ∞ σ.rotTwo z := by
  have e : σ.rotTwo = fun u => -exp ((σ.θ₂ : ℂ) * I) * mob σ.vertexTwo u :=
    funext (rotTwo_eq_mul_mob h)
  rw [e]
  exact contDiffAt_const.mul (contDiffAt_mob (one_sub_conj_mul_ne_zero
    (norm_vertexTwo_lt_one h) hz))

omit h in
theorem contDiff_wallSide_zero : ContDiff ℝ ∞ (σ.wallSide 0) := imCLM.contDiff

omit h in
theorem contDiff_wallSide_one : ContDiff ℝ ∞ (σ.wallSide 1) := by
  have e : σ.wallSide 1 = fun z => Real.sin σ.θ₃ * z.re - Real.cos σ.θ₃ * z.im :=
    funext wallSide_one_apply
  rw [e]
  exact (contDiff_const.mul reCLM.contDiff).sub (contDiff_const.mul imCLM.contDiff)

theorem contDiffAt_sideTwo {z : ℂ} (hz : ‖z‖ < 1) : ContDiffAt ℝ ∞ (sideTwo σ) z :=
  imCLM.contDiff.contDiffAt.comp z (contDiffAt_rotTwo h hz)

theorem hd_ne_zero_of_domZeroThree {z : ℂ} (hz : z ∈ domZeroThree σ) :
    hd σ 2 z ≠ 0 ∧ hd σ 1 z ≠ 0 :=
  ⟨norm_ne_zero_iff.2 (ne_zero_of_mem_pairDom hz), norm_ne_zero_iff.2
    (mob_ne_zero_of_mem_pairDom (sideTwoThree_pos h) (sideTwoThree_lt_one h) hz)⟩

theorem hd_ne_zero_of_domOneThree {z : ℂ} (hz : z ∈ domOneThree σ) :
    hd σ 2 z ≠ 0 ∧ hd σ 0 z ≠ 0 := by
  have a := ne_zero_of_mem_pairDom hz
  have b := mob_ne_zero_of_mem_pairDom (sideOneThree_pos h) (sideOneThree_lt_one h) hz
  refine ⟨?_, ?_⟩
  · change ‖z‖ ≠ 0
    rw [← norm_exp_neg_mul]
    exact norm_ne_zero_iff.2 a
  · change ‖mob σ.vertexOne z‖ ≠ 0
    rw [norm_mob_vertexOne_eq]
    exact norm_ne_zero_iff.2 b

theorem hd_ne_zero_of_domOneTwo {z : ℂ} (hz : z ∈ domOneTwo σ) :
    hd σ 1 z ≠ 0 ∧ hd σ 0 z ≠ 0 := by
  have a := ne_zero_of_mem_pairDom hz.2
  have b := mob_ne_zero_of_mem_pairDom (sideOneTwo_pos h) (sideOneTwo_lt_one h) hz.2
  refine ⟨?_, ?_⟩
  · change ‖mob σ.vertexTwo z‖ ≠ 0
    rw [← norm_rotTwo h]
    exact norm_ne_zero_iff.2 a
  · change ‖mob σ.vertexOne z‖ ≠ 0
    have h1 := norm_disc_vertexOne_eq h hz.1
    rw [CompactShape.disc_eq_mob h] at h1
    rw [h1]
    exact norm_ne_zero_iff.2 b

theorem contDiffAt_cofZeroThree {z : ℂ} (hz : z ∈ domZeroThree σ) :
    ContDiffAt ℝ ∞ (cofZeroThree σ) z :=
  contDiffAt_pairCof (sideTwoThree_pos h) (sideTwoThree_lt_one h) (tauThree_pos h)
    tauThree_lt_one (tauTwo_pos h) tauTwo_lt_one hz

theorem contDiffAt_cofOneThree {z : ℂ} (hz : z ∈ domOneThree σ) :
    ContDiffAt ℝ ∞ (cofOneThree σ) z :=
  (contDiffAt_pairCof (sideOneThree_pos h) (sideOneThree_lt_one h) (tauThree_pos h)
    tauThree_lt_one (tauOne_pos h) tauOne_lt_one hz).comp z
    (contDiffAt_const.mul contDiffAt_id)

theorem contDiffAt_cofTwo {z : ℂ} (hz : z ∈ domOneTwo σ) : ContDiffAt ℝ ∞ (cofTwo σ) z :=
  (contDiffAt_pairCof (sideOneTwo_pos h) (sideOneTwo_lt_one h) (tauTwo_pos h)
    tauTwo_lt_one (tauOne_pos h) tauOne_lt_one hz.2).comp z (contDiffAt_rotTwo h hz.1)

theorem contDiffAt_bridgeOne {z : ℂ} (hz : z ∈ domOneThree σ) :
    ContDiffAt ℝ ∞ (bridgeOne σ) z := by
  have hz1 := norm_lt_one_of_domOneThree hz
  have hv := hd_ne_zero_of_domOneThree h hz
  have h0 := contDiffAt_canon h 0 hz1 hv.2
  have h2 := contDiffAt_canon h 2 hz1 hv.1
  have hA : ContDiffAt ℝ ∞ (modThree σ) z := contDiffAt_const.sub (contDiffAt_const.mul h2)
  have hB : ContDiffAt ℝ ∞ (modOne σ) z := contDiffAt_const.add (contDiffAt_const.mul h0)
  have hP : ContDiffAt ℝ ∞ (cofBridgeOne σ) z :=
    ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
      (contDiffAt_const.mul (contDiffAt_cofOneThree h hz))
  exact contDiffAt_twoCircle hA hB contDiff_wallSide_one.contDiffAt hP
    (cofBridgeOne_pos h hz) (by norm_num)

theorem contDiffAt_bridgeZero {z : ℂ} (hz : z ∈ domZeroThree σ) :
    ContDiffAt ℝ ∞ (bridgeZero σ) z := by
  have hz1 := norm_lt_one_of_domZeroThree hz
  have hv := hd_ne_zero_of_domZeroThree h hz
  have h1 := contDiffAt_canon h 1 hz1 hv.2
  have h2 := contDiffAt_canon h 2 hz1 hv.1
  have hA : ContDiffAt ℝ ∞ (modThree σ) z := contDiffAt_const.sub (contDiffAt_const.mul h2)
  have hB : ContDiffAt ℝ ∞ (modTwo σ) z := contDiffAt_const.add (contDiffAt_const.mul h1)
  have hP : ContDiffAt ℝ ∞ (cofBridgeZero σ) z :=
    ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
      (contDiffAt_const.mul (contDiffAt_cofZeroThree h hz))
  exact contDiffAt_twoCircle hA hB contDiff_wallSide_zero.contDiffAt hP
    (cofBridgeZero_pos h hz) (by norm_num)

theorem contDiffAt_bridgeTwo {z : ℂ} (hz : z ∈ domOneTwo σ) :
    ContDiffAt ℝ ∞ (bridgeTwo σ) z := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have hv := hd_ne_zero_of_domOneTwo h hz
  have h0 := contDiffAt_canon h 0 hz1 hv.2
  have h1 := contDiffAt_canon h 1 hz1 hv.1
  have hA : ContDiffAt ℝ ∞ (modOne σ) z := contDiffAt_const.add (contDiffAt_const.mul h0)
  have hB : ContDiffAt ℝ ∞ (modTwo σ) z := contDiffAt_const.add (contDiffAt_const.mul h1)
  have hP : ContDiffAt ℝ ∞ (cofBridgeTwo σ) z :=
    (((hA.add hB).add contDiffAt_const).mul (contDiffAt_const.sub ((hA.sub hB).pow 2))).mul
      (contDiffAt_const.mul (contDiffAt_cofTwo h hz))
  exact contDiffAt_twoCircle hA hB (contDiffAt_sideTwo h hz1) hP
    (cofBridgeTwo_pos h hz) (by norm_num)

theorem isOpen_domZeroThree : IsOpen (domZeroThree σ) :=
  isOpen_pairDom (sideTwoThree_pos h) (sideTwoThree_lt_one h)

theorem isOpen_domOneThree : IsOpen (domOneThree σ) :=
  (isOpen_pairDom (sideOneThree_pos h) (sideOneThree_lt_one h)).preimage
    (continuous_const.mul continuous_id)

theorem isOpen_domOneTwo : IsOpen (domOneTwo σ) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have h1 : Metric.ball (0 : ℂ) 1 ∈ nhds z :=
    Metric.isOpen_ball.mem_nhds (by simpa using hz.1)
  have h2 := (contDiffAt_rotTwo h hz.1).continuousAt.preimage_mem_nhds
    ((isOpen_pairDom (sideOneTwo_pos h) (sideOneTwo_lt_one h)).mem_nhds hz.2)
  filter_upwards [h1, h2] with u hu1 hu2
  exact ⟨by simpa using hu1, hu2⟩

end Hyp

end HypFold

end GC.Seifert
