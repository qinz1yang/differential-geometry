import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphCanon
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldBridge

/-!
# Profile and bridges of the spherical compact fold

Lane CF-S, tier 2, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §3). The moduli are linear in the profile functions
`sphCanon j = tan ((dⱼ - rⱼ)/2)` with slope `compactProfileSlope = 2/5`:
`sphModOne = 3/2 + κ T₁` (about `+3/2`), `sphModTwo = 3/2 + κ T₂` (about `-3/2`) and
`sphModThree = 3 - κ T₃` (about `0`); on the triangle `|Tⱼ| < 1`, so the first two lie in
`(11/10, 19/10)` and the third in `(13/5, 17/5)` (`sphModOne_mem`, …).

Each wall has a coordinate `ζ` in which its first vertex is `0` and its second vertex is `t > 0`:
`ζ = z` (wall 0), `ζ = e^{-iθ₃} z` (wall 1), `ζ = rotTwo z` (wall 2). In it the sum of the two
profile functions is `(Im ζ)² · sphPairCof t τᵢ τⱼ ζ` (`sphCanon_add_*_cof`), and `sphPairDom t` is
an
open set of `ζ` (`isOpen_pairDom_sph`) on which the cofactor is smooth and positive. The bridges are
A4's `twoCircle` with this factorisation: `sphBridgeOne` (wall 1, circles `|u| = R₃`,
`|u - 3/2| = R₁`, side `wallSide 1`), `sphBridgeZero` (wall 0, `|u| = R₃`, `|u + 3/2| = R₂`, side
`wallSide 0`) and `sphBridgeTwo` (wall 2, `|u - 3/2| = R₁`, `|u + 3/2| = R₂`, side
`Im rotTwo`). On the open domains `sphDomOne`, `sphDomZero`, `sphDomTwo`, which contain the
triangle minus the two vertices of the wall, each bridge is smooth, lies on its two circles and
has the sign of its side function as the sign of its imaginary part; it satisfies the wall
identity `bridge ∘ refl = conj ∘ bridge`. On the triangle `Re sphBridgeOne > 0`,
`Re sphBridgeZero < 0`, `‖sphBridgeTwo‖ < 3/2` and `‖sphBridgeOne‖, ‖sphBridgeZero‖ > 13/5`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem contDiffAt_sphMoeb {a z : ℂ} (h : 1 + conj a * z ≠ 0) :
    ContDiffAt ℝ ∞ (sphMoeb a) z := by
  have h1 : ContDiffAt ℂ ∞ (fun w : ℂ => w - a) z := contDiffAt_id.sub contDiffAt_const
  have h2 : ContDiffAt ℂ ∞ (fun w : ℂ => 1 + conj a * w) z :=
    contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)
  exact (h1.div h2 h).restrict_scalars ℝ

theorem contDiff_re_sph' : ContDiff ℝ ∞ (fun z : ℂ => z.re) := reCLM.contDiff

theorem contDiff_im_sph' : ContDiff ℝ ∞ (fun z : ℂ => z.im) := imCLM.contDiff

theorem one_add_real_mul_ne_sph {t : ℝ} {ζ : ℂ} (h : 0 < 1 + t * ζ.re) : (1 : ℂ) + t * ζ ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, zero_re] at this
  linarith

def sphPairDom (t : ℝ) : Set ℂ :=
  {ζ | 0 < ‖ζ‖ + ζ.re ∧ 0 < 1 + t * ζ.re ∧ 0 < sphPairNum t ζ ∧ 0 < sphPairQ t ζ ∧ ‖ζ‖ < 2 ∧
    ‖sphMoeb t ζ‖ < 2}

def sphPairCof (t a b : ℝ) (ζ : ℂ) : ℝ :=
  (1 - a * b) * sphPairQ t ζ / ((1 + ‖ζ‖ * a) * (1 + ‖sphMoeb t ζ‖ * b))

theorem ne_zero_of_pos_norm_add_re_sph {ζ : ℂ} (h : 0 < ‖ζ‖ + ζ.re) : ζ ≠ 0 := by
  rintro rfl
  simp at h

theorem sphMoeb_ne_zero_of_pairNum {t : ℝ} {ζ : ℂ} (h2 : 0 < 1 + t * ζ.re)
    (h3 : 0 < sphPairNum t ζ) : sphMoeb t ζ ≠ 0 := by
  intro h0
  have hne := one_add_real_mul_ne_sph h2
  have hζ : ζ = t := by
    rw [sphMoeb, Complex.conj_ofReal, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 hne
  unfold sphPairNum at h3
  rw [h0, norm_zero, hζ, ofReal_re] at h3
  linarith

theorem contDiffAt_norm_sphMoeb_real {t : ℝ} {ζ : ℂ} (h2 : 0 < 1 + t * ζ.re)
    (hne : sphMoeb t ζ ≠ 0) : ContDiffAt ℝ ∞ (fun w : ℂ => ‖sphMoeb t w‖) ζ :=
  (contDiffAt_sphMoeb (by rw [Complex.conj_ofReal]; exact one_add_real_mul_ne_sph h2)).norm ℝ hne

theorem contDiffAt_pairNum_sph {t : ℝ} {ζ : ℂ} (h2 : 0 < 1 + t * ζ.re) (hne : sphMoeb t ζ ≠ 0) :
    ContDiffAt ℝ ∞ (sphPairNum t) ζ := by
  have hr : ContDiffAt ℝ ∞ (fun w : ℂ => w.re) ζ := contDiff_re_sph'.contDiffAt
  exact ((contDiffAt_const.add (contDiffAt_const.mul hr)).mul
    (contDiffAt_norm_sphMoeb_real h2 hne)).add contDiffAt_const |>.sub hr

theorem contDiffAt_pairQ_sph {t : ℝ} {ζ : ℂ} (h1 : 0 < ‖ζ‖ + ζ.re) (h2 : 0 < 1 + t * ζ.re)
    (h3 : 0 < sphPairNum t ζ) : ContDiffAt ℝ ∞ (sphPairQ t) ζ := by
  have hne := sphMoeb_ne_zero_of_pairNum h2 h3
  have hr : ContDiffAt ℝ ∞ (fun w : ℂ => w.re) ζ := contDiff_re_sph'.contDiffAt
  have hi : ContDiffAt ℝ ∞ (fun w : ℂ => w.im) ζ := contDiff_im_sph'.contDiffAt
  have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) ζ :=
    contDiffAt_norm ℝ (ne_zero_of_pos_norm_add_re_sph h1)
  have hm := contDiffAt_norm_sphMoeb_real h2 hne
  have hN : (fun w : ℂ => Complex.normSq (1 + t * w)) =
      fun w : ℂ => (1 + t * w.re) ^ 2 + t ^ 2 * w.im ^ 2 := funext (normSq_one_add_real_sph t)
  have hNs : ContDiffAt ℝ ∞ (fun w : ℂ => Complex.normSq (1 + t * w)) ζ := by
    rw [hN]
    exact ((contDiffAt_const.add (contDiffAt_const.mul hr)).pow 2).add
      (contDiffAt_const.mul (hi.pow 2))
  have hNpos : 0 < Complex.normSq (1 + t * ζ) := by
    rw [normSq_one_add_real_sph]
    positivity
  exact ((contDiffAt_const.add (contDiffAt_const.mul hm)).div (hn.add hr) h1.ne').add
    ((contDiffAt_const.mul ((contDiffAt_const.add (contDiffAt_const.mul hr)).sub
      contDiffAt_const)).div (hNs.mul (contDiffAt_pairNum_sph h2 hne))
      (mul_ne_zero hNpos.ne' h3.ne'))

theorem isOpen_pairDom_sph (t : ℝ) : IsOpen (sphPairDom t) := by
  rw [isOpen_iff_mem_nhds]
  intro ζ hζ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hζ
  have hne := sphMoeb_ne_zero_of_pairNum h2 h3
  have c1 : ContinuousAt (fun w : ℂ => ‖w‖ + w.re) ζ := by fun_prop
  have c2 : ContinuousAt (fun w : ℂ => 1 + t * w.re) ζ := by fun_prop
  have c3 : ContinuousAt (sphPairNum t) ζ := (contDiffAt_pairNum_sph h2 hne).continuousAt
  have c4 : ContinuousAt (sphPairQ t) ζ := (contDiffAt_pairQ_sph h1 h2 h3).continuousAt
  have c5 : ContinuousAt (fun w : ℂ => ‖w‖) ζ := by fun_prop
  have c6 : ContinuousAt (fun w : ℂ => ‖sphMoeb t w‖) ζ :=
    (contDiffAt_norm_sphMoeb_real h2 hne).continuousAt
  filter_upwards [continuousAt_const.eventually_lt c1 h1, continuousAt_const.eventually_lt c2 h2,
    continuousAt_const.eventually_lt c3 h3, continuousAt_const.eventually_lt c4 h4,
    c5.eventually_lt continuousAt_const h5, c6.eventually_lt continuousAt_const h6]
    with w e1 e2 e3 e4 e5 e6
  exact ⟨e1, e2, e3, e4, e5, e6⟩

theorem pairCof_pos_sph {t a b : ℝ} {ζ : ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b < 1)
    (hQ : 0 < sphPairQ t ζ) : 0 < sphPairCof t a b ζ := by
  have := norm_nonneg ζ
  have := norm_nonneg (sphMoeb (t : ℂ) ζ)
  have h1 : 0 < 1 - a * b := by linarith
  unfold sphPairCof
  positivity

theorem norm_sphMoeb_real_conj (t : ℝ) (ζ : ℂ) : ‖sphMoeb t (conj ζ)‖ = ‖sphMoeb t ζ‖ := by
  conv_lhs => rw [← Complex.conj_ofReal]
  rw [sphMoeb_conj, Complex.norm_conj]

theorem pairNum_conj_sph (t : ℝ) (ζ : ℂ) : sphPairNum t (conj ζ) = sphPairNum t ζ := by
  rw [sphPairNum, sphPairNum, norm_sphMoeb_real_conj, Complex.conj_re]

theorem pairQ_conj_sph (t : ℝ) (ζ : ℂ) : sphPairQ t (conj ζ) = sphPairQ t ζ := by
  rw [sphPairQ, sphPairQ, norm_sphMoeb_real_conj, Complex.conj_re, Complex.norm_conj,
      pairNum_conj_sph,
    normSq_one_add_real_sph, normSq_one_add_real_sph, Complex.conj_re, Complex.conj_im]
  ring

theorem pairCof_conj_sph (t a b : ℝ) (ζ : ℂ) : sphPairCof t a b (conj ζ) = sphPairCof t a b ζ := by
  rw [sphPairCof, sphPairCof, pairQ_conj_sph, Complex.norm_conj, norm_sphMoeb_real_conj]

theorem contDiffAt_pairCof_sph {t a b : ℝ} {ζ : ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hζ : ζ ∈ sphPairDom t)
    :
    ContDiffAt ℝ ∞ (sphPairCof t a b) ζ := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := hζ
  have hne := sphMoeb_ne_zero_of_pairNum h2 h3
  have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) ζ :=
    contDiffAt_norm ℝ (ne_zero_of_pos_norm_add_re_sph h1)
  have hm := contDiffAt_norm_sphMoeb_real h2 hne
  have hd : 0 < (1 + ‖ζ‖ * a) * (1 + ‖sphMoeb (t : ℂ) ζ‖ * b) := by
    have := norm_nonneg ζ
    have := norm_nonneg (sphMoeb (t : ℂ) ζ)
    positivity
  exact (contDiffAt_const.mul (contDiffAt_pairQ_sph h1 h2 h3)).div
    ((contDiffAt_const.add (hn.mul contDiffAt_const)).mul
      (contDiffAt_const.add (hm.mul contDiffAt_const))) hd.ne'


namespace CompactShape

variable {σ : CompactShape}

def sphModOne (σ : CompactShape) (z : ℂ) : ℝ := 3 / 2 + compactProfileSlope * σ.sphCanon 0 z

def sphModTwo (σ : CompactShape) (z : ℂ) : ℝ := 3 / 2 + compactProfileSlope * σ.sphCanon 1 z

def sphModThree (σ : CompactShape) (z : ℂ) : ℝ := 3 - compactProfileSlope * σ.sphCanon 2 z

def sphSideTwo (σ : CompactShape) (z : ℂ) : ℝ := (σ.rotTwo z).im

def sphCofZero (σ : CompactShape) (z : ℂ) : ℝ :=
  sphPairCof σ.sphTTwoThree (σ.sphTau 2) (σ.sphTau 1) z

def sphCofOne (σ : CompactShape) (z : ℂ) : ℝ :=
  sphPairCof σ.sphTOneThree (σ.sphTau 2) (σ.sphTau 0) (exp (-((σ.θ₃ : ℂ) * I)) * z)

def sphCofTwo (σ : CompactShape) (z : ℂ) : ℝ :=
  sphPairCof σ.sphTOneTwo (σ.sphTau 1) (σ.sphTau 0) (σ.rotTwo z)

def sphCofBridgeOne (σ : CompactShape) (z : ℂ) : ℝ :=
  ((σ.sphModThree z + σ.sphModOne z) ^ 2 - 9 / 4) * (3 / 2 + σ.sphModThree z - σ.sphModOne z) *
    (compactProfileSlope * σ.sphCofOne z)

def sphCofBridgeZero (σ : CompactShape) (z : ℂ) : ℝ :=
  ((σ.sphModThree z + σ.sphModTwo z) ^ 2 - 9 / 4) * (3 / 2 + σ.sphModThree z - σ.sphModTwo z) *
    (compactProfileSlope * σ.sphCofZero z)

def sphCofBridgeTwo (σ : CompactShape) (z : ℂ) : ℝ :=
  (σ.sphModOne z + σ.sphModTwo z + 3) * (9 - (σ.sphModOne z - σ.sphModTwo z) ^ 2) *
    (compactProfileSlope * σ.sphCofTwo z)

def sphBridgeOne (σ : CompactShape) (z : ℂ) : ℂ :=
  twoCircle 0 (3 / 2) (σ.sphModThree z) (σ.sphModOne z) (σ.wallSide 1 z) (σ.sphCofBridgeOne z)

def sphBridgeZero (σ : CompactShape) (z : ℂ) : ℂ :=
  twoCircle 0 (-(3 / 2)) (σ.sphModThree z) (σ.sphModTwo z) (σ.wallSide 0 z)
    (σ.sphCofBridgeZero z)

def sphBridgeTwo (σ : CompactShape) (z : ℂ) : ℂ :=
  twoCircle (3 / 2) (-(3 / 2)) (σ.sphModOne z) (σ.sphModTwo z) (σ.sphSideTwo z)
    (σ.sphCofBridgeTwo z)

def sphDomZero (σ : CompactShape) : Set ℂ := {z | z ∈ sphPairDom σ.sphTTwoThree}

def sphDomOne (σ : CompactShape) : Set ℂ :=
  {z | exp (-((σ.θ₃ : ℂ) * I)) * z ∈ sphPairDom σ.sphTOneThree}

def sphDomTwo (σ : CompactShape) : Set ℂ :=
  {z | 1 + σ.vertexTwo * z ≠ 0 ∧ 1 + conj σ.vertexOne * z ≠ 0 ∧
    σ.rotTwo z ∈ sphPairDom σ.sphTOneTwo}

theorem isOpen_sphDomZero : IsOpen σ.sphDomZero := isOpen_pairDom_sph _

theorem isOpen_sphDomOne : IsOpen σ.sphDomOne :=
  (isOpen_pairDom_sph _).preimage (continuous_const.mul continuous_id)

theorem sphDist_two_eq (z : ℂ) : σ.sphDist 2 z = ‖exp (-((σ.θ₃ : ℂ) * I)) * z‖ :=
  (norm_exp_neg_mul_sph z).symm

theorem exp_neg_mul_refl_one_sph (z : ℂ) :
    exp (-((σ.θ₃ : ℂ) * I)) * σ.refl 1 z = conj (exp (-((σ.θ₃ : ℂ) * I)) * z) := by
  rw [refl_one_apply_sph, map_mul, conj_exp_neg_sph, exp_two_mul_eq_sph]
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination (exp ((σ.θ₃ : ℂ) * I) * conj z) * this

theorem sphCofZero_refl_zero (z : ℂ) : σ.sphCofZero (σ.refl 0 z) = σ.sphCofZero z := by
  rw [sphCofZero, sphCofZero, refl_zero_apply_sph, pairCof_conj_sph]

theorem sphCofOne_refl_one (z : ℂ) : σ.sphCofOne (σ.refl 1 z) = σ.sphCofOne z := by
  rw [sphCofOne, sphCofOne, exp_neg_mul_refl_one_sph, pairCof_conj_sph]

theorem twoCircle_congr {a b A B w P A' B' w' P' : ℝ} (hA : A' = A) (hB : B' = B)
    (hw : w' = -w) (hP : P' = P) : twoCircle a b A' B' w' P' = conj (twoCircle a b A B w P) := by
  rw [hA, hB, hw, hP, twoCircle_neg]

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem rotTwo_eq_fun_sph : σ.rotTwo = fun w => -exp ((σ.θ₂ : ℂ) * I) * sphMoeb σ.vertexTwo w :=
  funext (rotTwo_eq_mul_sph hs)

theorem contDiffAt_rotTwo_sph {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0) :
    ContDiffAt ℝ ∞ σ.rotTwo z := by
  rw [rotTwo_eq_fun_sph hs]
  exact contDiffAt_const.mul (contDiffAt_sphMoeb (by rwa [conj_vertexTwo_sph]))

theorem isOpen_sphDomTwo : IsOpen σ.sphDomTwo := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hz
  have hc : ContinuousAt σ.rotTwo z := (contDiffAt_rotTwo_sph hs h1).continuousAt
  have c1 : ContinuousAt (fun w : ℂ => 1 + σ.vertexTwo * w) z := by fun_prop
  have c2 : ContinuousAt (fun w : ℂ => 1 + conj σ.vertexOne * w) z := by fun_prop
  filter_upwards [c1.eventually_ne h1, c2.eventually_ne h2,
    hc.preimage_mem_nhds ((isOpen_pairDom_sph _).mem_nhds h3)] with w e1 e2 e3
  exact ⟨e1, e2, e3⟩

theorem sphDist_one_eq (z : ℂ) : σ.sphDist 1 z = ‖sphMoeb σ.sphTTwoThree z‖ := by
  change ‖σ.rotTwo z‖ = _
  rw [norm_rotTwo_sph hs, vertexTwo_eq_sph]

theorem sphDist_zero_eq (z : ℂ) :
    σ.sphDist 0 z = ‖sphMoeb σ.sphTOneThree (exp (-((σ.θ₃ : ℂ) * I)) * z)‖ := by
  change ‖σ.rotOne z‖ = _
  rw [rotOne_eq_neg_sphMoeb hs, norm_neg]

theorem sphDist_zero_eq_two {z : ℂ} (h1 : 1 + conj σ.vertexOne * z ≠ 0)
    (h2 : 1 + σ.vertexTwo * z ≠ 0) :
    σ.sphDist 0 z = ‖sphMoeb σ.sphTOneTwo (σ.rotTwo z)‖ :=
  norm_rotOne_eq_sphMoeb_rotTwo hs h1 (by rwa [conj_vertexTwo_sph])

theorem sphCanon_add_zero_cof {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    σ.sphCanon 2 z + σ.sphCanon 1 z = σ.wallSide 0 z ^ 2 * σ.sphCofZero z := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := hz
  have hd2 : σ.sphDist 2 z = ‖z‖ := rfl
  rw [sphCanon_add_zero hs h1 h2 h3, sphCofZero, sphPairCof, sphDist_one_eq hs, hd2]
  ring

theorem sphCanon_add_one_cof {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    σ.sphCanon 2 z + σ.sphCanon 0 z = σ.wallSide 1 z ^ 2 * σ.sphCofOne z := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := hz
  rw [norm_exp_neg_mul_sph] at h1
  rw [sphCanon_add_one hs h1 h2 h3, sphCofOne, sphPairCof, sphDist_zero_eq hs, sphDist_two_eq]
  ring

theorem sphCanon_add_two_cof {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    σ.sphCanon 1 z + σ.sphCanon 0 z = σ.sphSideTwo z ^ 2 * σ.sphCofTwo z := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -⟩ := hz
  have hd1 : σ.sphDist 1 z = ‖σ.rotTwo z‖ := rfl
  rw [sphCanon_add_two hs h2 (by rwa [conj_vertexTwo_sph]) h3 h4 h5, sphCofTwo, sphPairCof,
    sphDist_zero_eq_two hs h2 h1, hd1, sphSideTwo]
  ring

theorem sphCofZero_pos {z : ℂ} (hz : z ∈ σ.sphDomZero) : 0 < σ.sphCofZero z :=
  pairCof_pos_sph (sphTau_pos hs 2).le (sphTau_pos hs 1).le (sphTau_mul_lt_one hs 2 1)
    hz.2.2.2.1

theorem sphCofOne_pos {z : ℂ} (hz : z ∈ σ.sphDomOne) : 0 < σ.sphCofOne z :=
  pairCof_pos_sph (sphTau_pos hs 2).le (sphTau_pos hs 0).le (sphTau_mul_lt_one hs 2 0)
    hz.2.2.2.1

theorem sphCofTwo_pos {z : ℂ} (hz : z ∈ σ.sphDomTwo) : 0 < σ.sphCofTwo z :=
  pairCof_pos_sph (sphTau_pos hs 1).le (sphTau_pos hs 0).le (sphTau_mul_lt_one hs 1 0)
    hz.2.2.2.2.2.1

theorem sphCanon_lt_two {j : Fin 3} {z : ℂ} (h : σ.sphDist j z < 2) : σ.sphCanon j z < 2 := by
  have hd := one_add_sphDist_mul_pos hs j z
  have := sphTau_pos hs j
  have := σ.sphDist_nonneg j z
  rw [sphCanon, div_lt_iff₀ hd]
  nlinarith

theorem sphCanon_bounds_zero {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    σ.sphCanon 1 z < 2 ∧ σ.sphCanon 2 z < 2 :=
  ⟨sphCanon_lt_two hs (by rw [sphDist_one_eq hs]; exact hz.2.2.2.2.2),
    sphCanon_lt_two hs (j := 2) hz.2.2.2.2.1⟩

theorem sphCanon_bounds_one {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    σ.sphCanon 0 z < 2 ∧ σ.sphCanon 2 z < 2 :=
  ⟨sphCanon_lt_two hs (by rw [sphDist_zero_eq hs]; exact hz.2.2.2.2.2),
    sphCanon_lt_two hs (by rw [sphDist_two_eq]; exact hz.2.2.2.2.1)⟩

theorem sphCanon_bounds_two {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    σ.sphCanon 0 z < 2 ∧ σ.sphCanon 1 z < 2 :=
  ⟨sphCanon_lt_two hs (by rw [sphDist_zero_eq_two hs hz.2.1 hz.1]; exact hz.2.2.2.2.2.2.2),
    sphCanon_lt_two hs (j := 1) hz.2.2.2.2.2.2.1⟩

theorem sphCofBridgeOne_pos {z : ℂ} (hz : z ∈ σ.sphDomOne) : 0 < σ.sphCofBridgeOne z := by
  have hc := sphCofOne_pos hs hz
  obtain ⟨h0, h2⟩ := sphCanon_bounds_one hs hz
  have g0 := neg_one_lt_sphCanon hs 0 z
  have g2 := neg_one_lt_sphCanon hs 2 z
  have e1 : 3 / 2 < σ.sphModThree z + σ.sphModOne z := by
    unfold sphModThree sphModOne compactProfileSlope
    linarith
  have e2 : 0 < 3 / 2 + σ.sphModThree z - σ.sphModOne z := by
    unfold sphModThree sphModOne compactProfileSlope
    linarith
  have e3 : 0 < (σ.sphModThree z + σ.sphModOne z) ^ 2 - 9 / 4 := by nlinarith
  unfold sphCofBridgeOne compactProfileSlope
  positivity

theorem sphCofBridgeZero_pos {z : ℂ} (hz : z ∈ σ.sphDomZero) : 0 < σ.sphCofBridgeZero z := by
  have hc := sphCofZero_pos hs hz
  obtain ⟨h1, h2⟩ := sphCanon_bounds_zero hs hz
  have g1 := neg_one_lt_sphCanon hs 1 z
  have g2 := neg_one_lt_sphCanon hs 2 z
  have e1 : 3 / 2 < σ.sphModThree z + σ.sphModTwo z := by
    unfold sphModThree sphModTwo compactProfileSlope
    linarith
  have e2 : 0 < 3 / 2 + σ.sphModThree z - σ.sphModTwo z := by
    unfold sphModThree sphModTwo compactProfileSlope
    linarith
  have e3 : 0 < (σ.sphModThree z + σ.sphModTwo z) ^ 2 - 9 / 4 := by nlinarith
  unfold sphCofBridgeZero compactProfileSlope
  positivity

theorem sphCofBridgeTwo_pos {z : ℂ} (hz : z ∈ σ.sphDomTwo) : 0 < σ.sphCofBridgeTwo z := by
  have hc := sphCofTwo_pos hs hz
  obtain ⟨h0, h1⟩ := sphCanon_bounds_two hs hz
  have g0 := neg_one_lt_sphCanon hs 0 z
  have g1 := neg_one_lt_sphCanon hs 1 z
  have e1 : 0 < σ.sphModOne z + σ.sphModTwo z + 3 := by
    unfold sphModOne sphModTwo compactProfileSlope
    linarith
  have e2 : 0 < 9 - (σ.sphModOne z - σ.sphModTwo z) ^ 2 := by
    have : σ.sphModOne z - σ.sphModTwo z =
        compactProfileSlope * (σ.sphCanon 0 z - σ.sphCanon 1 z) := by
      unfold sphModOne sphModTwo
      ring
    rw [this]
    unfold compactProfileSlope
    nlinarith
  unfold sphCofBridgeTwo compactProfileSlope
  positivity

theorem heron_sphBridgeOne {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    ((σ.sphModThree z + σ.sphModOne z) ^ 2 - (3 / 2 - 0) ^ 2) *
        ((3 / 2 - 0) ^ 2 - (σ.sphModThree z - σ.sphModOne z) ^ 2) =
      σ.wallSide 1 z ^ 2 * σ.sphCofBridgeOne z := by
  have h := sphCanon_add_one_cof hs hz
  have e : 3 / 2 - σ.sphModThree z + σ.sphModOne z =
      compactProfileSlope * (σ.sphCanon 2 z + σ.sphCanon 0 z) := by
    unfold sphModThree sphModOne
    ring
  rw [h] at e
  unfold sphCofBridgeOne
  have : (3 / 2 - 0 : ℝ) ^ 2 - (σ.sphModThree z - σ.sphModOne z) ^ 2 =
      (3 / 2 - σ.sphModThree z + σ.sphModOne z) * (3 / 2 + σ.sphModThree z - σ.sphModOne z) := by
    ring
  rw [this, e]
  ring

theorem heron_sphBridgeZero {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    ((σ.sphModThree z + σ.sphModTwo z) ^ 2 - (-(3 / 2) - 0) ^ 2) *
        ((-(3 / 2) - 0) ^ 2 - (σ.sphModThree z - σ.sphModTwo z) ^ 2) =
      σ.wallSide 0 z ^ 2 * σ.sphCofBridgeZero z := by
  have h := sphCanon_add_zero_cof hs hz
  have e : 3 / 2 - σ.sphModThree z + σ.sphModTwo z =
      compactProfileSlope * (σ.sphCanon 2 z + σ.sphCanon 1 z) := by
    unfold sphModThree sphModTwo
    ring
  rw [h] at e
  unfold sphCofBridgeZero
  have : (-(3 / 2) - 0 : ℝ) ^ 2 - (σ.sphModThree z - σ.sphModTwo z) ^ 2 =
      (3 / 2 - σ.sphModThree z + σ.sphModTwo z) * (3 / 2 + σ.sphModThree z - σ.sphModTwo z) := by
    ring
  rw [this, e]
  ring

theorem heron_sphBridgeTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    ((σ.sphModOne z + σ.sphModTwo z) ^ 2 - (-(3 / 2) - 3 / 2) ^ 2) *
        ((-(3 / 2) - 3 / 2) ^ 2 - (σ.sphModOne z - σ.sphModTwo z) ^ 2) =
      σ.sphSideTwo z ^ 2 * σ.sphCofBridgeTwo z := by
  have h := sphCanon_add_two_cof hs hz
  have e : σ.sphModOne z + σ.sphModTwo z - 3 =
      compactProfileSlope * (σ.sphCanon 1 z + σ.sphCanon 0 z) := by
    unfold sphModOne sphModTwo
    ring
  rw [h] at e
  unfold sphCofBridgeTwo
  have : (σ.sphModOne z + σ.sphModTwo z) ^ 2 - (-(3 / 2) - 3 / 2 : ℝ) ^ 2 =
      (σ.sphModOne z + σ.sphModTwo z - 3) * (σ.sphModOne z + σ.sphModTwo z + 3) := by ring
  rw [this, e]
  ring

theorem sphModOne_pos (z : ℂ) : 0 < σ.sphModOne z := by
  have := neg_one_lt_sphCanon hs 0 z
  unfold sphModOne compactProfileSlope
  linarith

theorem sphModTwo_pos (z : ℂ) : 0 < σ.sphModTwo z := by
  have := neg_one_lt_sphCanon hs 1 z
  unfold sphModTwo compactProfileSlope
  linarith

omit hs in
theorem sphModThree_pos {z : ℂ} (h : σ.sphCanon 2 z < 2) : 0 < σ.sphModThree z := by
  unfold sphModThree compactProfileSlope
  linarith

theorem norm_sphBridgeOne {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    ‖σ.sphBridgeOne z‖ = σ.sphModThree z ∧ ‖σ.sphBridgeOne z - 3 / 2‖ = σ.sphModOne z := by
  have hab : (0 : ℝ) ≠ 3 / 2 := by norm_num
  have hP := (sphCofBridgeOne_pos hs hz).le
  have hH := heron_sphBridgeOne hs hz
  constructor
  · have h := norm_twoCircle_sub_left hab hP
      (sphModThree_pos (sphCanon_bounds_one hs hz).2).le hH
    simpa [sphBridgeOne] using h
  · have h := norm_twoCircle_sub_right hab hP (sphModOne_pos hs z).le hH
    rw [sphBridgeOne]
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring] at h
    exact h

theorem norm_sphBridgeZero {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    ‖σ.sphBridgeZero z‖ = σ.sphModThree z ∧ ‖σ.sphBridgeZero z + 3 / 2‖ = σ.sphModTwo z := by
  have hab : (0 : ℝ) ≠ -(3 / 2) := by norm_num
  have hP := (sphCofBridgeZero_pos hs hz).le
  have hH := heron_sphBridgeZero hs hz
  constructor
  · have h := norm_twoCircle_sub_left hab hP
      (sphModThree_pos (sphCanon_bounds_zero hs hz).2).le hH
    simpa [sphBridgeZero] using h
  · have h := norm_twoCircle_sub_right hab hP (sphModTwo_pos hs z).le hH
    rw [sphBridgeZero]
    rw [show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add] at h
    exact h

theorem norm_sphBridgeTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    ‖σ.sphBridgeTwo z - 3 / 2‖ = σ.sphModOne z ∧ ‖σ.sphBridgeTwo z + 3 / 2‖ = σ.sphModTwo z := by
  have hab : (3 / 2 : ℝ) ≠ -(3 / 2) := by norm_num
  have hP := (sphCofBridgeTwo_pos hs hz).le
  have hH := heron_sphBridgeTwo hs hz
  constructor
  · have h := norm_twoCircle_sub_left hab hP (sphModOne_pos hs z).le hH
    rw [sphBridgeTwo]
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring] at h
    exact h
  · have h := norm_twoCircle_sub_right hab hP (sphModTwo_pos hs z).le hH
    rw [sphBridgeTwo]
    rw [show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add] at h
    exact h

theorem im_sphBridgeOne_pos {z : ℂ} (hz : z ∈ σ.sphDomOne) (hw : 0 < σ.wallSide 1 z) :
    0 < (σ.sphBridgeOne z).im :=
  twoCircle_im_pos (by norm_num) hw (sphCofBridgeOne_pos hs hz)

theorem im_sphBridgeZero_pos {z : ℂ} (hz : z ∈ σ.sphDomZero) (hw : 0 < σ.wallSide 0 z) :
    0 < (σ.sphBridgeZero z).im :=
  twoCircle_im_pos (by norm_num) hw (sphCofBridgeZero_pos hs hz)

theorem im_sphBridgeTwo_pos {z : ℂ} (hz : z ∈ σ.sphDomTwo) (hw : 0 < σ.sphSideTwo z) :
    0 < (σ.sphBridgeTwo z).im :=
  twoCircle_im_pos (by norm_num) hw (sphCofBridgeTwo_pos hs hz)

end Spherical

theorem im_sphBridgeOne_eq_zero {z : ℂ} (hw : σ.wallSide 1 z = 0) :
    (σ.sphBridgeOne z).im = 0 := by
  rw [sphBridgeOne, hw, twoCircle_im_eq_zero]

theorem im_sphBridgeZero_eq_zero {z : ℂ} (hw : σ.wallSide 0 z = 0) :
    (σ.sphBridgeZero z).im = 0 := by
  rw [sphBridgeZero, hw, twoCircle_im_eq_zero]

theorem im_sphBridgeTwo_eq_zero {z : ℂ} (hw : σ.sphSideTwo z = 0) :
    (σ.sphBridgeTwo z).im = 0 := by
  rw [sphBridgeTwo, hw, twoCircle_im_eq_zero]

theorem contDiffAt_exp_neg_mul (z : ℂ) :
    ContDiffAt ℝ ∞ (fun w : ℂ => exp (-((σ.θ₃ : ℂ) * I)) * w) z :=
  (contDiff_const.mul contDiff_id).contDiffAt

theorem contDiffAt_wallSide_zero_sph (z : ℂ) : ContDiffAt ℝ ∞ (σ.wallSide 0) z :=
  contDiff_im_sph'.contDiffAt

theorem contDiffAt_wallSide_one_sph (z : ℂ) : ContDiffAt ℝ ∞ (σ.wallSide 1) z := by
  have h : σ.wallSide 1 = fun w => Real.sin σ.θ₃ * w.re - Real.cos σ.θ₃ * w.im :=
    funext wallSide_one_apply_sph
  rw [h]
  exact (contDiffAt_const.mul contDiff_re_sph'.contDiffAt).sub
    (contDiffAt_const.mul contDiff_im_sph'.contDiffAt)

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem sphBridgeOne_refl_one (z : ℂ) : σ.sphBridgeOne (σ.refl 1 z) = conj (σ.sphBridgeOne z) := by
  have h0 := sphCanon_refl_one_zero hs z
  have h2 := sphCanon_refl_one_two (σ := σ) z
  rw [sphBridgeOne, sphBridgeOne]
  apply twoCircle_congr
  · rw [sphModThree, sphModThree, h2]
  · rw [sphModOne, sphModOne, h0]
  · exact wallSide_refl_one_sph z
  · rw [sphCofBridgeOne, sphCofBridgeOne, sphModThree, sphModThree, sphModOne, sphModOne, h0, h2,
      sphCofOne_refl_one]

theorem sphBridgeZero_refl_zero (z : ℂ) :
    σ.sphBridgeZero (σ.refl 0 z) = conj (σ.sphBridgeZero z) := by
  have h1 := sphCanon_refl_zero_one hs z
  have h2 := sphCanon_refl_zero_two (σ := σ) z
  rw [sphBridgeZero, sphBridgeZero]
  apply twoCircle_congr
  · rw [sphModThree, sphModThree, h2]
  · rw [sphModTwo, sphModTwo, h1]
  · exact wallSide_refl_zero_sph z
  · rw [sphCofBridgeZero, sphCofBridgeZero, sphModThree, sphModThree, sphModTwo, sphModTwo, h1,
      h2, sphCofZero_refl_zero]

theorem sphSideTwo_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    σ.sphSideTwo (σ.refl 2 z) = -σ.sphSideTwo z := by
  rw [sphSideTwo, sphSideTwo, rotTwo_refl_two_sph hs hz, Complex.conj_im]

theorem sphCofTwo_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    σ.sphCofTwo (σ.refl 2 z) = σ.sphCofTwo z := by
  rw [sphCofTwo, sphCofTwo, rotTwo_refl_two_sph hs hz, pairCof_conj_sph]

theorem sphBridgeTwo_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (h1 : 1 + conj σ.vertexOne * z ≠ 0) :
    σ.sphBridgeTwo (σ.refl 2 z) = conj (σ.sphBridgeTwo z) := by
  have h0 := sphCanon_refl_two_zero hs hz h1
  have h1' := sphCanon_refl_two_one hs hz
  rw [sphBridgeTwo, sphBridgeTwo]
  apply twoCircle_congr
  · rw [sphModOne, sphModOne, h0]
  · rw [sphModTwo, sphModTwo, h1']
  · exact sphSideTwo_refl_two hs hz
  · rw [sphCofBridgeTwo, sphCofBridgeTwo, sphModOne, sphModOne, sphModTwo, sphModTwo, h0, h1',
      sphCofTwo_refl_two hs hz]

theorem contDiffAt_sphCanon_of {j : Fin 3} {z : ℂ} {d : ℂ → ℝ} (hd : ContDiffAt ℝ ∞ d z)
    (he : ∀ᶠ w in 𝓝 z, σ.sphDist j w = d w) : ContDiffAt ℝ ∞ (σ.sphCanon j) z := by
  have hz : σ.sphDist j z = d z := he.self_of_nhds
  have hpos : 0 < 1 + d z * σ.sphTau j := by
    rw [← hz]
    exact one_add_sphDist_mul_pos hs j z
  have h : ContDiffAt ℝ ∞ (fun w => (d w - σ.sphTau j) / (1 + d w * σ.sphTau j)) z :=
    (hd.sub contDiffAt_const).div (contDiffAt_const.add (hd.mul contDiffAt_const)) hpos.ne'
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [he] with w hw
  rw [sphCanon, hw]

theorem contDiffAt_sphSideTwo {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0) :
    ContDiffAt ℝ ∞ σ.sphSideTwo z :=
  contDiff_im_sph'.contDiffAt.comp z (contDiffAt_rotTwo_sph hs h)

theorem contDiffAt_sphBridgeZero {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    ContDiffAt ℝ ∞ σ.sphBridgeZero z := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := id hz
  have hne := sphMoeb_ne_zero_of_pairNum h2 h3
  have c1 : ContDiffAt ℝ ∞ (σ.sphCanon 1) z :=
    contDiffAt_sphCanon_of hs (contDiffAt_norm_sphMoeb_real h2 hne)
      (Filter.Eventually.of_forall (sphDist_one_eq hs))
  have c2 : ContDiffAt ℝ ∞ (σ.sphCanon 2) z :=
    contDiffAt_sphCanon_of hs (d := fun w => ‖w‖)
      (contDiffAt_norm ℝ (ne_zero_of_pos_norm_add_re_sph h1))
      (Filter.Eventually.of_forall fun w => rfl)
  have hA : ContDiffAt ℝ ∞ σ.sphModThree z := contDiffAt_const.sub (contDiffAt_const.mul c2)
  have hB : ContDiffAt ℝ ∞ σ.sphModTwo z := contDiffAt_const.add (contDiffAt_const.mul c1)
  have hC : ContDiffAt ℝ ∞ σ.sphCofZero z :=
    contDiffAt_pairCof_sph (sphTau_pos hs 2).le (sphTau_pos hs 1).le hz
  have hP : ContDiffAt ℝ ∞ σ.sphCofBridgeZero z :=
    ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
      (contDiffAt_const.mul hC)
  exact contDiffAt_twoCircle hA hB (contDiffAt_wallSide_zero_sph z) hP
    (sphCofBridgeZero_pos hs hz) (by norm_num)

theorem contDiffAt_sphBridgeOne {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    ContDiffAt ℝ ∞ σ.sphBridgeOne z := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := id hz
  have hne := sphMoeb_ne_zero_of_pairNum h2 h3
  have hL := contDiffAt_exp_neg_mul (σ := σ) z
  have c0 : ContDiffAt ℝ ∞ (σ.sphCanon 0) z :=
    contDiffAt_sphCanon_of hs
      (d := fun w => ‖sphMoeb σ.sphTOneThree (exp (-((σ.θ₃ : ℂ) * I)) * w)‖)
      ((contDiffAt_norm_sphMoeb_real h2 hne).comp z hL)
      (Filter.Eventually.of_forall (sphDist_zero_eq hs))
  have c2 : ContDiffAt ℝ ∞ (σ.sphCanon 2) z :=
    contDiffAt_sphCanon_of hs (d := fun w => ‖exp (-((σ.θ₃ : ℂ) * I)) * w‖)
      ((contDiffAt_norm ℝ (ne_zero_of_pos_norm_add_re_sph h1)).comp z hL)
      (Filter.Eventually.of_forall sphDist_two_eq)
  have hA : ContDiffAt ℝ ∞ σ.sphModThree z := contDiffAt_const.sub (contDiffAt_const.mul c2)
  have hB : ContDiffAt ℝ ∞ σ.sphModOne z := contDiffAt_const.add (contDiffAt_const.mul c0)
  have hC : ContDiffAt ℝ ∞ σ.sphCofOne z :=
    (contDiffAt_pairCof_sph (sphTau_pos hs 2).le (sphTau_pos hs 0).le hz).comp z hL
  have hP : ContDiffAt ℝ ∞ σ.sphCofBridgeOne z :=
    ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
      (contDiffAt_const.mul hC)
  exact contDiffAt_twoCircle hA hB (contDiffAt_wallSide_one_sph z) hP
    (sphCofBridgeOne_pos hs hz) (by norm_num)

theorem contDiffAt_sphBridgeTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    ContDiffAt ℝ ∞ σ.sphBridgeTwo z := by
  obtain ⟨hv2, hv1, h1, h2, h3, h4, h5, h6⟩ := id hz
  have hne := sphMoeb_ne_zero_of_pairNum h2 h3
  have hR := contDiffAt_rotTwo_sph hs hv2
  have hev : ∀ᶠ w in 𝓝 z, σ.sphDist 0 w = ‖sphMoeb σ.sphTOneTwo (σ.rotTwo w)‖ := by
    have c1 : ContinuousAt (fun w : ℂ => 1 + σ.vertexTwo * w) z := by fun_prop
    have c2 : ContinuousAt (fun w : ℂ => 1 + conj σ.vertexOne * w) z := by fun_prop
    filter_upwards [c1.eventually_ne hv2, c2.eventually_ne hv1] with w e1 e2
    exact sphDist_zero_eq_two hs e2 e1
  have c0 : ContDiffAt ℝ ∞ (σ.sphCanon 0) z :=
    contDiffAt_sphCanon_of hs ((contDiffAt_norm_sphMoeb_real h2 hne).comp z hR) hev
  have c1 : ContDiffAt ℝ ∞ (σ.sphCanon 1) z :=
    contDiffAt_sphCanon_of hs (d := fun w => ‖σ.rotTwo w‖)
      (hR.norm ℝ (ne_zero_of_pos_norm_add_re_sph h1)) (Filter.Eventually.of_forall fun w => rfl)
  have hA : ContDiffAt ℝ ∞ σ.sphModOne z := contDiffAt_const.add (contDiffAt_const.mul c0)
  have hB : ContDiffAt ℝ ∞ σ.sphModTwo z := contDiffAt_const.add (contDiffAt_const.mul c1)
  have hC : ContDiffAt ℝ ∞ σ.sphCofTwo z :=
    (contDiffAt_pairCof_sph (sphTau_pos hs 1).le (sphTau_pos hs 0).le
      hz.2.2).comp z hR
  have hP : ContDiffAt ℝ ∞ σ.sphCofBridgeTwo z :=
    (((hA.add hB).add contDiffAt_const).mul (contDiffAt_const.sub ((hA.sub hB).pow 2))).mul
      (contDiffAt_const.mul hC)
  exact contDiffAt_twoCircle hA hB (contDiffAt_sphSideTwo hs hv2) hP
    (sphCofBridgeTwo_pos hs hz) (by norm_num)

theorem mem_sphDomZero {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h2 : z ≠ σ.vertexTwo) :
    z ∈ σ.sphDomZero := by
  obtain ⟨c1, c2, c3, c4⟩ := conditions_zero_sph hs hz h0 h2
  refine ⟨c1, c2, c3, c4, by linarith [norm_le_one_of_mem_sph hs hz], ?_⟩
  rw [← sphDist_one_eq hs]
  linarith [sphDist_le_one_of_mem hs 1 hz]

theorem mem_sphDomOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) :
    z ∈ σ.sphDomOne := by
  obtain ⟨c1, c2, c3, c4⟩ := conditions_one_sph hs hz h0 h1
  rw [← norm_exp_neg_mul_sph z] at c1
  refine ⟨c1, c2, c3, c4, ?_, ?_⟩
  · rw [norm_exp_neg_mul_sph]
    linarith [norm_le_one_of_mem_sph hs hz]
  · rw [← sphDist_zero_eq hs]
    linarith [sphDist_le_one_of_mem hs 0 hz]

theorem mem_sphDomTwo {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) : z ∈ σ.sphDomTwo := by
  have hv2 := one_add_vertexTwo_ne_sph hs hz
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  obtain ⟨c1, c2, c3, c4⟩ := conditions_two_sph hs hz h1 h2
  refine ⟨hv2, hv1, c1, c2, c3, c4, by linarith [norm_rotTwo_le_one_sph hs hz], ?_⟩
  rw [← sphDist_zero_eq_two hs hv1 hv2]
  linarith [sphDist_le_one_of_mem hs 0 hz]

theorem sphModOne_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    11 / 10 < σ.sphModOne z ∧ σ.sphModOne z < 19 / 10 := by
  obtain ⟨h1, h2⟩ := sphCanon_mem hs 0 hz
  unfold sphModOne compactProfileSlope
  constructor <;> linarith

theorem sphModTwo_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    11 / 10 < σ.sphModTwo z ∧ σ.sphModTwo z < 19 / 10 := by
  obtain ⟨h1, h2⟩ := sphCanon_mem hs 1 hz
  unfold sphModTwo compactProfileSlope
  constructor <;> linarith

theorem sphModThree_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    13 / 5 < σ.sphModThree z ∧ σ.sphModThree z < 17 / 5 := by
  obtain ⟨h1, h2⟩ := sphCanon_mem hs 2 hz
  unfold sphModThree compactProfileSlope
  constructor <;> linarith

theorem re_sphBridgeOne_pos {z : ℂ} (hz : z ∈ σ.triangle) : 0 < (σ.sphBridgeOne z).re := by
  have hA := sphModThree_mem hs hz
  have hB := sphModOne_mem hs hz
  rw [sphBridgeOne, twoCircle_re]
  have : 0 < σ.sphModThree z ^ 2 - σ.sphModOne z ^ 2 + (3 / 2 - 0) ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < 2 * (3 / 2 - 0) := by norm_num
  have := div_pos this h2
  linarith

theorem re_sphBridgeZero_neg {z : ℂ} (hz : z ∈ σ.triangle) : (σ.sphBridgeZero z).re < 0 := by
  have hA := sphModThree_mem hs hz
  have hB := sphModTwo_mem hs hz
  rw [sphBridgeZero, twoCircle_re]
  have : 0 < σ.sphModThree z ^ 2 - σ.sphModTwo z ^ 2 + (-(3 / 2) - 0) ^ 2 := by nlinarith
  have h2 : 2 * (-(3 / 2) - 0 : ℝ) < 0 := by norm_num
  have := div_neg_of_pos_of_neg this h2
  linarith

theorem norm_sphBridgeOne_gt {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) : 13 / 5 < ‖σ.sphBridgeOne z‖ := by
  rw [(norm_sphBridgeOne hs (mem_sphDomOne hs hz h0 h1)).1]
  exact (sphModThree_mem hs hz).1

theorem norm_sphBridgeZero_gt {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h2 : z ≠ σ.vertexTwo) : 13 / 5 < ‖σ.sphBridgeZero z‖ := by
  rw [(norm_sphBridgeZero hs (mem_sphDomZero hs hz h0 h2)).1]
  exact (sphModThree_mem hs hz).1

theorem norm_sphBridgeTwo_lt {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) : ‖σ.sphBridgeTwo z‖ < 3 / 2 := by
  obtain ⟨e1, e2⟩ := norm_sphBridgeTwo hs (mem_sphDomTwo hs hz h1 h2)
  have hA := sphModOne_mem hs hz
  have hB := sphModTwo_mem hs hz
  have q1 := sq_norm_eq_sph (σ.sphBridgeTwo z - 3 / 2)
  have q2 := sq_norm_eq_sph (σ.sphBridgeTwo z + 3 / 2)
  have q := sq_norm_eq_sph (σ.sphBridgeTwo z)
  rw [e1] at q1
  rw [e2] at q2
  simp only [sub_re, add_re, sub_im, add_im, div_ofNat_re, div_ofNat_im, Complex.re_ofNat,
    Complex.im_ofNat, zero_div, sub_zero, add_zero] at q1 q2
  have hsq : ‖σ.sphBridgeTwo z‖ ^ 2 < (3 / 2) ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

end Spherical


end CompactShape

end GC.Seifert
