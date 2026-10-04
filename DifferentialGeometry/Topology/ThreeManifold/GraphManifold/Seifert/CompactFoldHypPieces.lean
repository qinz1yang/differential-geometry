import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypLayout
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypWalls

/-!
# The pieces of the hyperbolic compact fold

Lane CF-H3, tier 3 (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, curvature `-1`, with review 23 §6.1: a gluing
certificate made of open sets on which the fold is given by one smooth formula with positive
Jacobian). The map is `hypPreFold σ (hypLayout σ)` of `CompactFoldHypPreFold` with the layout of
`CompactFoldHypLayout`.

Nine open pieces of the unit disc carry one formula each (`hypPreFold_eq_*`): the apex models on
the germ discs `hd j < g` (disjoint, `g_lt_hd_zero_of_apexTwo`, by the reverse pseudo-hyperbolic
triangle inequality `pseudo_triangle_rev`), the outer germ on `0 < ‖z‖ < g₃`, the corners on the
corner regions `canon j < -e`, the bridge `bridgeTwo` on the lens, the corner at `v₃` outside, and
the bridges `bridgeOne`, `bridgeZero` on the junctions across the corner boundaries above the
switch. Each piece lies in the open set where its formula is smooth and has positive Jacobian
(`validOne`, …: a smoothness domain intersected with `{0 < det}`, open because the derivative is
continuous there, `isOpen_det_pos`). The union `hypGoodSet σ` is open and `hypPreFold` is smooth
there with positive Jacobian off `v₁`, `v₂` (`contDiffAt_hypPreFold`, `det_hypPreFold_pos`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

theorem pseudo_triangle_rev {τ : ℝ} {Z : ℂ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hZ : ‖Z‖ < 1) :
    τ - ‖Z‖ ≤ ‖mob (τ : ℂ) Z‖ * (1 - τ * ‖Z‖) := by
  have hXr := Complex.abs_re_le_norm Z
  rw [abs_le] at hXr
  have hw0 := norm_nonneg Z
  have hm0 := norm_nonneg (mob (τ : ℂ) Z)
  have h1 : 0 < 1 - τ * ‖Z‖ := by nlinarith
  rcases le_or_gt τ ‖Z‖ with hle | hlt
  · nlinarith
  have hD0 : 0 < 1 - τ * Z.re := by nlinarith
  have hne : 1 - (τ : ℂ) * Z ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      zero_re] at this
    linarith
  have hsq := norm_mob_ofReal_sq hne
  have hD : 0 < (1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2 := by positivity
  have hr : ‖Z‖ ^ 2 = Z.re ^ 2 + Z.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  have hid : ((Z.re - τ) ^ 2 + Z.im ^ 2) * (1 - τ * ‖Z‖) ^ 2 -
      (τ - ‖Z‖) ^ 2 * ((1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2) =
        (1 - τ ^ 2) * (1 - ‖Z‖ ^ 2) * (2 * τ * (‖Z‖ - Z.re)) := by
    have : Z.im ^ 2 = ‖Z‖ ^ 2 - Z.re ^ 2 := by linarith
    rw [this]; ring
  have hnn : 0 ≤ (1 - τ ^ 2) * (1 - ‖Z‖ ^ 2) * (2 * τ * (‖Z‖ - Z.re)) := by
    have a1 : 0 ≤ 1 - τ ^ 2 := by nlinarith
    have a2 : 0 ≤ 1 - ‖Z‖ ^ 2 := by nlinarith
    have a3 : 0 ≤ 2 * τ * (‖Z‖ - Z.re) := mul_nonneg (by positivity) (by linarith)
    positivity
  have e2 : (‖mob (τ : ℂ) Z‖ * (1 - τ * ‖Z‖)) ^ 2 * ((1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2) =
      ((Z.re - τ) ^ 2 + Z.im ^ 2) * (1 - τ * ‖Z‖) ^ 2 := by
    rw [← hsq]; ring
  have key : (τ - ‖Z‖) ^ 2 ≤ (‖mob (τ : ℂ) Z‖ * (1 - τ * ‖Z‖)) ^ 2 := by
    have : (τ - ‖Z‖) ^ 2 * ((1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2) ≤
        (‖mob (τ : ℂ) Z‖ * (1 - τ * ‖Z‖)) ^ 2 * ((1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2) := by
      linarith
    exact le_of_mul_le_mul_right this hD
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) key

theorem sub_le_norm_mob {τ : ℝ} {Z : ℂ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hZ : ‖Z‖ < 1) :
    τ - ‖Z‖ ≤ ‖mob (τ : ℂ) Z‖ := by
  have h := pseudo_triangle_rev hτ0 hτ1 hZ
  have hm0 := norm_nonneg (mob (τ : ℂ) Z)
  have : ‖mob (τ : ℂ) Z‖ * (1 - τ * ‖Z‖) ≤ ‖mob (τ : ℂ) Z‖ :=
    mul_le_of_le_one_right hm0 (by nlinarith [norm_nonneg Z])
  linarith

theorem le_oplus_left {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) :
    a ≤ oplus a b := by
  rw [oplus, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hb0 (by nlinarith : (0 : ℝ) ≤ 1 - a ^ 2)]

theorem continuousAt_det_fderiv {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    ContinuousAt (fun u => (fderiv ℝ f u).det) z :=
  ContinuousLinearMap.continuous_det.continuousAt.comp
    (hf.fderiv_right (m := 0) (by simp)).continuousAt

theorem ev_lt' {f : ℂ → ℝ} {z : ℂ} {a : ℝ} (hf : ContinuousAt f z) (h : a < f z) :
    ∀ᶠ u in 𝓝 z, a < f u := hf.eventually (lt_mem_nhds h)

theorem ev_gt' {f : ℂ → ℝ} {z : ℂ} {a : ℝ} (hf : ContinuousAt f z) (h : f z < a) :
    ∀ᶠ u in 𝓝 z, f u < a := hf.eventually (gt_mem_nhds h)

theorem ev_det_pos {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z)
    (h : 0 < (fderiv ℝ f z).det) : ∀ᶠ u in 𝓝 z, 0 < (fderiv ℝ f u).det :=
  ev_lt' (continuousAt_det_fderiv hf) h

variable (σ : CompactShape)

def smoothOne : Set ℂ :=
  {z | z ∈ domOneThree σ ∧ z ∈ domOneTwo σ ∧ 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re ∧
    0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2) ∧
    0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2)}

def smoothTwo : Set ℂ :=
  {z | z ∈ domOneTwo σ ∧ z ∈ domZeroThree σ ∧ 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re ∧
    0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2) ∧
    0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2)}

def smoothThree : Set ℂ :=
  {z | z ∈ domOneThree σ ∧ z ∈ domZeroThree σ ∧ 0 < ‖z‖ + z.re ∧
    0 < modThree σ z + (bridgeOne σ z).re ∧ 0 < modThree σ z - (bridgeZero σ z).re}

def foldCornerOne : ℂ → ℂ :=
  cornerOne σ (hypLayout σ).a (hypLayout σ).b (hypLayout σ).β (hypLayout σ).β'

def foldCornerTwo : ℂ → ℂ :=
  cornerTwo σ (hypLayout σ).a (hypLayout σ).b (hypLayout σ).β (hypLayout σ).β'

def foldCornerThree : ℂ → ℂ := cornerThree σ (hypLayout σ).a₃ (hypLayout σ).b₃ 1 (hypLayout σ).e

def validOne : Set ℂ := {z | z ∈ smoothOne σ ∧ 0 < (fderiv ℝ (foldCornerOne σ) z).det}

def validTwo : Set ℂ := {z | z ∈ smoothTwo σ ∧ 0 < (fderiv ℝ (foldCornerTwo σ) z).det}

def validThree : Set ℂ := {z | z ∈ smoothThree σ ∧ 0 < (fderiv ℝ (foldCornerThree σ) z).det}

def validLens : Set ℂ :=
  {z | z ∈ domOneTwo σ ∧ 0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2) ∧
    0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2) ∧ 0 < (fderiv ℝ (bridgeTwo σ) z).det}

def validJunctionOne : Set ℂ :=
  {z | z ∈ domOneThree σ ∧ 0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2) ∧
    0 < modThree σ z + (bridgeOne σ z).re ∧ 0 < (fderiv ℝ (bridgeOne σ) z).det}

def validJunctionTwo : Set ℂ :=
  {z | z ∈ domZeroThree σ ∧ 0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2) ∧
    0 < modThree σ z - (bridgeZero σ z).re ∧ 0 < (fderiv ℝ (bridgeZero σ) z).det}

def pieceApexOne : Set ℂ := {z | ‖z‖ < 1 ∧ hd σ 0 z < (hypLayout σ).g}

def pieceApexTwo : Set ℂ := {z | ‖z‖ < 1 ∧ hd σ 1 z < (hypLayout σ).g}

def pieceOuter : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ < (hypLayout σ).g₃}

def pieceCornerOne : Set ℂ :=
  {z | ‖z‖ < 1 ∧ (hypLayout σ).g / 2 < hd σ 0 z ∧ canon σ 0 z < -(hypLayout σ).e ∧
    (hypLayout σ).g < hd σ 1 z ∧ (hypLayout σ).g₃ < ‖z‖ ∧ z ∈ validOne σ}

def pieceCornerTwo : Set ℂ :=
  {z | ‖z‖ < 1 ∧ (hypLayout σ).g / 2 < hd σ 1 z ∧ canon σ 1 z < -(hypLayout σ).e ∧
    (hypLayout σ).g < hd σ 0 z ∧ (hypLayout σ).g₃ < ‖z‖ ∧ -(hypLayout σ).e < canon σ 0 z ∧
    z ∈ validTwo σ}

def pieceLens : Set ℂ :=
  {z | ‖z‖ < 1 ∧ (hypLayout σ).b < hd σ 0 z ∧ (hypLayout σ).b < hd σ 1 z ∧
    |lensCoord σ z| < (hypLayout σ).β ∧ (hypLayout σ).g₃ < ‖z‖ ∧ z ∈ validLens σ}

def pieceCornerThree : Set ℂ :=
  {z | ‖z‖ < 1 ∧ -(hypLayout σ).e < canon σ 0 z ∧ -(hypLayout σ).e < canon σ 1 z ∧
    (hypLayout σ).β < |lensCoord σ z| ∧ (hypLayout σ).g₃ / 2 < ‖z‖ ∧
    (hypLayout σ).g < hd σ 0 z ∧ (hypLayout σ).g < hd σ 1 z ∧ z ∈ validThree σ}

def pieceJunctionOne : Set ℂ :=
  {z | ‖z‖ < 1 ∧ (hypLayout σ).b < hd σ 0 z ∧ -(hypLayout σ).e < canon σ 1 z ∧
    (hypLayout σ).β' < lensCoord σ z ∧ (hypLayout σ).b₃ < ‖z‖ ∧ 0 < ‖z‖ + z.re ∧
    1 < blendThree σ 1 (hypLayout σ).e z ∧ (hypLayout σ).g < hd σ 1 z ∧
    z ∈ validJunctionOne σ}

def pieceJunctionTwo : Set ℂ :=
  {z | ‖z‖ < 1 ∧ (hypLayout σ).b < hd σ 1 z ∧ -(hypLayout σ).e < canon σ 0 z ∧
    (hypLayout σ).β' < lensCoord σ z ∧ (hypLayout σ).b₃ < ‖z‖ ∧ 0 < ‖z‖ + z.re ∧
    blendThree σ 1 (hypLayout σ).e z < -1 ∧ (hypLayout σ).g < hd σ 0 z ∧
    z ∈ validJunctionTwo σ}

def hypGoodSet : Set ℂ :=
  pieceApexOne σ ∪ pieceApexTwo σ ∪ pieceOuter σ ∪ pieceCornerOne σ ∪ pieceCornerTwo σ ∪
    pieceLens σ ∪ pieceCornerThree σ ∪ pieceJunctionOne σ ∪ pieceJunctionTwo σ

variable {σ}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem hd_zero_eq_mob_rotTwo {z : ℂ} (hz : ‖z‖ < 1) :
    hd σ 0 z = ‖mob (sideOneTwo σ : ℂ) (σ.rotTwo z)‖ := by
  rw [← norm_rotOne_eq_hd h, rotOne_eq_mob_rotTwo h hz, norm_mul, norm_neg_exp, one_mul]

theorem tauMin_le_sideOneTwo : tauMin σ ≤ sideOneTwo σ := by
  rw [← oplus_tauOne_tauTwo h]
  exact le_trans tauMin_le_one
    (le_oplus_left (tauOne_pos h).le tauOne_lt_one (tauTwo_pos h).le)

theorem far_of_hd_lt {z : ℂ} (hz : ‖z‖ < 1) :
    sideOneTwo σ - hd σ 1 z ≤ hd σ 0 z := by
  rw [hd_zero_eq_mob_rotTwo h hz, ← norm_rotTwo_eq_hd h]
  exact sub_le_norm_mob (sideOneTwo_pos h).le (sideOneTwo_lt_one h) (norm_rotTwo_lt_one h hz)

theorem g_lt_hd_zero_of_apexTwo {z : ℂ} (hz : ‖z‖ < 1) (h1 : hd σ 1 z < (hypLayout σ).g) :
    (hypLayout σ).g < hd σ 0 z := by
  have := far_of_hd_lt h hz
  have := tauMin_le_sideOneTwo h
  have := tauMin_pos h
  simp only [hypLayout] at *
  linarith

theorem g_lt_hd_one_of_apexOne {z : ℂ} (hz : ‖z‖ < 1) (h0 : hd σ 0 z < (hypLayout σ).g) :
    (hypLayout σ).g < hd σ 1 z := by
  have := far_of_hd_lt h hz
  have := tauMin_le_sideOneTwo h
  have := tauMin_pos h
  simp only [hypLayout] at *
  linarith

theorem g_lt_hd_of_outer {z : ℂ} (hz : ‖z‖ < (hypLayout σ).g₃) :
    (hypLayout σ).g < hd σ 0 z ∧ (hypLayout σ).g < hd σ 1 z := by
  have hp := hypLayout_params h
  have hm := tauMin_pos h
  have hτ3 := tauThree_pos h
  have hg3 : (hypLayout σ).g₃ ≤ tauThree σ / 8 := by
    have : outerEnd σ ≤ tauThree σ / 2 := min_le_left _ _
    simp only [hypLayout]; linarith
  have hz1 : ‖z‖ < 1 := by linarith [hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have t13a : tauOne σ ≤ sideOneThree σ := by
    rw [← oplus_tauOne_tauThree h]
    exact le_oplus_left (tauOne_pos h).le tauOne_lt_one hτ3.le
  have t13b : tauThree σ ≤ sideOneThree σ := by
    rw [← oplus_tauOne_tauThree h, oplus_comm]
    exact le_oplus_left hτ3.le tauThree_lt_one (tauOne_pos h).le
  have t23a : tauTwo σ ≤ sideTwoThree σ := by
    rw [← oplus_tauTwo_tauThree h]
    exact le_oplus_left (tauTwo_pos h).le tauTwo_lt_one hτ3.le
  have t23b : tauThree σ ≤ sideTwoThree σ := by
    rw [← oplus_tauTwo_tauThree h, oplus_comm]
    exact le_oplus_left hτ3.le tauThree_lt_one (tauTwo_pos h).le
  have m1 := tauMin_le_one (σ := σ)
  have m2 := tauMin_le_two (σ := σ)
  have e1 : hd σ 0 z = ‖mob (sideOneThree σ : ℂ) (exp (-((σ.θ₃ : ℂ) * I)) * z)‖ := by
    have hu : ‖exp ((σ.θ₃ : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have := mob_mul_mul hu (sideOneThree σ : ℂ) (exp (-((σ.θ₃ : ℂ) * I)) * z)
    rw [← mul_assoc, exp_mul_exp_neg, one_mul, mul_comm (exp _)] at this
    change ‖mob σ.vertexOne z‖ = _
    rw [vertexOne_eq, this, norm_mul, hu, one_mul]
  have e0 : hd σ 1 z = ‖mob (sideTwoThree σ : ℂ) z‖ := rfl
  have n1 : ‖exp (-((σ.θ₃ : ℂ) * I)) * z‖ = ‖z‖ := by
    rw [norm_mul, norm_exp_neg_ofReal_mul_I, one_mul]
  have b1 := sub_le_norm_mob (sideOneThree_pos h).le (sideOneThree_lt_one h) (n1 ▸ hz1)
  have b2 := sub_le_norm_mob (sideTwoThree_pos h).le (sideTwoThree_lt_one h) hz1
  rw [n1] at b1
  rw [← e1] at b1
  rw [← e0] at b2
  simp only [hypLayout] at *
  constructor <;> linarith

omit h in
theorem hypPreFold_eq_apexOne {z : ℂ} (hz : z ∈ pieceApexOne σ) :
    hypPreFold σ (hypLayout σ) z = 3 / 2 + σ.rotOne z ^ σ.p₁ / 2 := by
  rw [hypPreFold, ite_eq_left hz.2]

theorem hypPreFold_eq_apexTwo {z : ℂ} (hz : z ∈ pieceApexTwo σ) :
    hypPreFold σ (hypLayout σ) z = -(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2 := by
  rw [hypPreFold, ite_eq_right (not_lt.2 (g_lt_hd_zero_of_apexTwo h hz.1 hz.2).le),
    ite_eq_left hz.2]

theorem hypPreFold_eq_outerPiece {z : ℂ}
    (hz : z ∈ pieceOuter σ) :
    hypPreFold σ (hypLayout σ) z = compactOuterGerm σ.p₃ z := by
  obtain ⟨a0, a1⟩ := g_lt_hd_of_outer h hz.2
  rw [hypPreFold, ite_eq_right (not_lt.2 a0.le), ite_eq_right (not_lt.2 a1.le), ite_eq_left hz.2]

theorem hypPreFold_eq_cornerOne {z : ℂ} (hz : z ∈ pieceCornerOne σ) :
    hypPreFold σ (hypLayout σ) z = foldCornerOne σ z := by
  obtain ⟨hz1, -, hc, h1, h3, ⟨⟨-, -, hψ, -, -⟩, -⟩⟩ := hz
  have hp := hypLayout_params h
  obtain ⟨hg0, hga, hab, -⟩ := hp
  by_cases hlt : hd σ 0 z < (hypLayout σ).g
  · rw [hypPreFold, ite_eq_left hlt, foldCornerOne,
      cornerOne_eq_apexOne h hab (by linarith) (by linarith) (Or.inr hψ)]
  · rw [hypPreFold, ite_eq_right hlt, ite_eq_right (not_lt.2 h1.le),
      ite_eq_right (not_lt.2 h3.le), ite_eq_left hc]
    rfl

theorem hypPreFold_eq_cornerTwo {z : ℂ} (hz : z ∈ pieceCornerTwo σ) :
    hypPreFold σ (hypLayout σ) z = foldCornerTwo σ z := by
  obtain ⟨hz1, -, hc, h0, h3, hc0, ⟨⟨-, -, hψ, -, -⟩, -⟩⟩ := hz
  have hp := hypLayout_params h
  obtain ⟨hg0, hga, hab, -⟩ := hp
  rw [hypPreFold, ite_eq_right (not_lt.2 h0.le)]
  by_cases hlt : hd σ 1 z < (hypLayout σ).g
  · rw [ite_eq_left hlt, foldCornerTwo,
      cornerTwo_eq_apexTwo h hab (by linarith) (by linarith) (Or.inr hψ)]
  · rw [ite_eq_right hlt, ite_eq_right (not_lt.2 h3.le), ite_eq_right (not_lt.2 hc0.le),
      ite_eq_left hc]
    rfl

theorem hypPreFold_eq_lens {z : ℂ} (hz : z ∈ pieceLens σ) :
    hypPreFold σ (hypLayout σ) z = bridgeTwo σ z := by
  obtain ⟨hz1, h0, h1, hl, h3, ⟨hz2, hp1, hp2, -⟩⟩ := hz
  obtain ⟨hg0, hga, hab, -, -, -, -, -, hββ, -⟩ := hypLayout_params h
  have hl' : lensCoord σ z ≤ (hypLayout σ).β := le_trans (le_abs_self _) hl.le
  rw [hypPreFold, ite_eq_right (not_lt.2 (by linarith)), ite_eq_right (not_lt.2 (by linarith)),
    ite_eq_right (not_lt.2 h3.le)]
  by_cases c0 : canon σ 0 z < -(hypLayout σ).e
  · rw [ite_eq_left c0]
    exact cornerOne_eq_bridgeTwo h hab hββ hz2 hp1 h0.le hl'
  rw [ite_eq_right c0]
  by_cases c1 : canon σ 1 z < -(hypLayout σ).e
  · rw [ite_eq_left c1]
    exact cornerTwo_eq_bridgeTwo h hab hββ hz2 hp2 h1.le hl'
  rw [ite_eq_right c1, ite_eq_left hl]

theorem hypPreFold_eq_cornerThree {z : ℂ} (hz : z ∈ pieceCornerThree σ) :
    hypPreFold σ (hypLayout σ) z = foldCornerThree σ z := by
  obtain ⟨hz1, c0, c1, hl, -, h0, h1, ⟨⟨-, -, hψ, -, -⟩, -⟩⟩ := hz
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hg3a, ha3b, -⟩ := hypLayout_params h
  rw [hypPreFold, ite_eq_right (not_lt.2 h0.le), ite_eq_right (not_lt.2 h1.le)]
  by_cases hlt : ‖z‖ < (hypLayout σ).g₃
  · rw [ite_eq_left hlt, foldCornerThree, cornerThree_eq_outerGerm ha3b (by linarith) hψ]
  · rw [ite_eq_right hlt, ite_eq_right (not_lt.2 c0.le), ite_eq_right (not_lt.2 c1.le),
      ite_eq_right (not_lt.2 hl.le)]
    rfl

theorem hypPreFold_eq_junctionOne {z : ℂ} (hz : z ∈ pieceJunctionOne σ) :
    hypPreFold σ (hypLayout σ) z = bridgeOne σ z := by
  obtain ⟨hz1, h0, c1, hl, h3, -, hν, h1, ⟨hd1, hp1, hp3, -⟩⟩ := hz
  obtain ⟨hg0, hga, hab, -, -, -, -, hβ0, hββ, -, -, -, hg3a, ha3b, -⟩ := hypLayout_params h
  rw [hypPreFold, ite_eq_right (not_lt.2 (by linarith)), ite_eq_right (not_lt.2 h1.le),
    ite_eq_right (not_lt.2 (by linarith))]
  by_cases c0 : canon σ 0 z < -(hypLayout σ).e
  · rw [ite_eq_left c0]
    exact cornerOne_eq_bridgeOne h hab hββ hd1 hp1 h0.le hl.le
  rw [ite_eq_right c0, ite_eq_right (not_lt.2 c1.le), ite_eq_right (not_lt.2 (by
    rw [abs_of_pos (by linarith)]; linarith))]
  exact cornerThree_eq_bridgeOne h ha3b one_pos hd1 hp3 h3.le hν.le

theorem hypPreFold_eq_junctionTwo {z : ℂ} (hz : z ∈ pieceJunctionTwo σ) :
    hypPreFold σ (hypLayout σ) z = bridgeZero σ z := by
  obtain ⟨hz1, h1, c0, hl, h3, -, hν, h0, ⟨hd0, hp0, hp3, -⟩⟩ := hz
  obtain ⟨hg0, hga, hab, -, -, -, -, hβ0, hββ, -, -, -, hg3a, ha3b, -⟩ := hypLayout_params h
  rw [hypPreFold, ite_eq_right (not_lt.2 h0.le), ite_eq_right (not_lt.2 (by linarith)),
    ite_eq_right (not_lt.2 (by linarith)), ite_eq_right (not_lt.2 c0.le)]
  by_cases c1 : canon σ 1 z < -(hypLayout σ).e
  · rw [ite_eq_left c1]
    exact cornerTwo_eq_bridgeZero h hab hββ hd0 hp0 h1.le hl.le
  rw [ite_eq_right c1, ite_eq_right (not_lt.2 (by rw [abs_of_pos (by linarith)]; linarith))]
  exact cornerThree_eq_bridgeZero h ha3b one_pos hd0 hp3 h3.le hν.le

theorem contAt_modOne {z : ℂ} (hz : ‖z‖ < 1) : ContinuousAt (modOne σ) z :=
  continuousAt_const.add (continuousAt_const.mul (continuousAt_canon_of_disc h 0 hz))

theorem contAt_modTwo {z : ℂ} (hz : ‖z‖ < 1) : ContinuousAt (modTwo σ) z :=
  continuousAt_const.add (continuousAt_const.mul (continuousAt_canon_of_disc h 1 hz))

theorem contAt_modThree {z : ℂ} (hz : ‖z‖ < 1) : ContinuousAt (modThree σ) z :=
  continuousAt_const.sub (continuousAt_const.mul (continuousAt_canon_of_disc h 2 hz))

theorem contAt_reBridgeOne {z : ℂ} (hz : z ∈ domOneThree σ) :
    ContinuousAt (fun u => (bridgeOne σ u).re) z :=
  Complex.continuous_re.continuousAt.comp (contDiffAt_bridgeOne h hz).continuousAt

theorem contAt_reBridgeTwo {z : ℂ} (hz : z ∈ domOneTwo σ) :
    ContinuousAt (fun u => (bridgeTwo σ u).re) z :=
  Complex.continuous_re.continuousAt.comp (contDiffAt_bridgeTwo h hz).continuousAt

theorem contAt_reBridgeZero {z : ℂ} (hz : z ∈ domZeroThree σ) :
    ContinuousAt (fun u => (bridgeZero σ u).re) z :=
  Complex.continuous_re.continuousAt.comp (contDiffAt_bridgeZero h hz).continuousAt

omit h in
theorem contAt_normAddRe_comp {f : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z) :
    ContinuousAt (fun u => ‖f u‖ + (f u).re) z :=
  (continuous_norm.continuousAt.comp hf).add (Complex.continuous_re.continuousAt.comp hf)

theorem isOpen_smoothOne : IsOpen (smoothOne σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨h1, h2, hψ, hp1, hp2⟩ := hz
  have hz1 := norm_lt_one_of_domOneThree h1
  filter_upwards [(isOpen_domOneThree h).mem_nhds h1, (isOpen_domOneTwo h).mem_nhds h2,
    ev_lt' (contAt_normAddRe_comp (contDiffAt_rotOne h hz1).continuousAt) hψ,
    ev_lt' ((contAt_modOne h hz1).add ((contAt_reBridgeOne h h1).sub continuousAt_const)) hp1,
    ev_lt' ((contAt_modOne h hz1).sub ((contAt_reBridgeTwo h h2).sub continuousAt_const)) hp2]
    with u a b c d e
  exact ⟨a, b, c, d, e⟩

theorem isOpen_smoothTwo : IsOpen (smoothTwo σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨h2, h0, hψ, hp2, hp0⟩ := hz
  have hz1 := norm_lt_one_of_domOneTwo h2
  filter_upwards [(isOpen_domOneTwo h).mem_nhds h2, (isOpen_domZeroThree h).mem_nhds h0,
    ev_lt' (contAt_normAddRe_comp (contDiffAt_rotTwo h hz1).continuousAt) hψ,
    ev_lt' ((contAt_modTwo h hz1).add ((contAt_reBridgeTwo h h2).add continuousAt_const)) hp2,
    ev_lt' ((contAt_modTwo h hz1).sub ((contAt_reBridgeZero h h0).add continuousAt_const)) hp0]
    with u a b c d e
  exact ⟨a, b, c, d, e⟩

theorem isOpen_smoothThree : IsOpen (smoothThree σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨h1, h0, hψ, hp1, hp0⟩ := hz
  have hz1 := norm_lt_one_of_domOneThree h1
  filter_upwards [(isOpen_domOneThree h).mem_nhds h1, (isOpen_domZeroThree h).mem_nhds h0,
    ev_lt' (contAt_normAddRe_comp continuousAt_id) hψ,
    ev_lt' ((contAt_modThree h hz1).add (contAt_reBridgeOne h h1)) hp1,
    ev_lt' ((contAt_modThree h hz1).sub (contAt_reBridgeZero h h0)) hp0]
    with u a b c d e
  exact ⟨a, b, c, d, e⟩

theorem contDiffAt_foldCornerOne {z : ℂ} (hz : z ∈ smoothOne σ) :
    ContDiffAt ℝ ∞ (foldCornerOne σ) z :=
  contDiffAt_cornerOne h _ _ _ _ hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2

theorem contDiffAt_foldCornerTwo {z : ℂ} (hz : z ∈ smoothTwo σ) :
    ContDiffAt ℝ ∞ (foldCornerTwo σ) z :=
  contDiffAt_cornerTwo h _ _ _ _ hz.1 hz.2.1 hz.2.2.2.1 hz.2.2.2.2

theorem contDiffAt_foldCornerThree {z : ℂ} (hz : z ∈ smoothThree σ) :
    ContDiffAt ℝ ∞ (foldCornerThree σ) z :=
  contDiffAt_cornerThree h _ _ _ _ hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2

theorem isOpen_validOne : IsOpen (validOne σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  filter_upwards [(isOpen_smoothOne h).mem_nhds hz.1,
    ev_det_pos (contDiffAt_foldCornerOne h hz.1) hz.2] with u a b
  exact ⟨a, b⟩

theorem isOpen_validTwo : IsOpen (validTwo σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  filter_upwards [(isOpen_smoothTwo h).mem_nhds hz.1,
    ev_det_pos (contDiffAt_foldCornerTwo h hz.1) hz.2] with u a b
  exact ⟨a, b⟩

theorem isOpen_validThree : IsOpen (validThree σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  filter_upwards [(isOpen_smoothThree h).mem_nhds hz.1,
    ev_det_pos (contDiffAt_foldCornerThree h hz.1) hz.2] with u a b
  exact ⟨a, b⟩

theorem isOpen_validLens : IsOpen (validLens σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨h2, hp1, hp2, hd⟩ := hz
  have hz1 := norm_lt_one_of_domOneTwo h2
  filter_upwards [(isOpen_domOneTwo h).mem_nhds h2,
    ev_lt' ((contAt_modOne h hz1).sub ((contAt_reBridgeTwo h h2).sub continuousAt_const)) hp1,
    ev_lt' ((contAt_modTwo h hz1).add ((contAt_reBridgeTwo h h2).add continuousAt_const)) hp2,
    ev_det_pos (contDiffAt_bridgeTwo h h2) hd] with u a b c d
  exact ⟨a, b, c, d⟩

theorem isOpen_validJunctionOne : IsOpen (validJunctionOne σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨h1, hp1, hp3, hd⟩ := hz
  have hz1 := norm_lt_one_of_domOneThree h1
  filter_upwards [(isOpen_domOneThree h).mem_nhds h1,
    ev_lt' ((contAt_modOne h hz1).add ((contAt_reBridgeOne h h1).sub continuousAt_const)) hp1,
    ev_lt' ((contAt_modThree h hz1).add (contAt_reBridgeOne h h1)) hp3,
    ev_det_pos (contDiffAt_bridgeOne h h1) hd] with u a b c d
  exact ⟨a, b, c, d⟩

theorem isOpen_validJunctionTwo : IsOpen (validJunctionTwo σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨h0, hp0, hp3, hd⟩ := hz
  have hz1 := norm_lt_one_of_domZeroThree h0
  filter_upwards [(isOpen_domZeroThree h).mem_nhds h0,
    ev_lt' ((contAt_modTwo h hz1).sub ((contAt_reBridgeZero h h0).add continuousAt_const)) hp0,
    ev_lt' ((contAt_modThree h hz1).sub (contAt_reBridgeZero h h0)) hp3,
    ev_det_pos (contDiffAt_bridgeZero h h0) hd] with u a b c d
  exact ⟨a, b, c, d⟩

omit h in
theorem contAt_norm' (z : ℂ) : ContinuousAt (fun u : ℂ => ‖u‖) z :=
  continuous_norm.continuousAt

theorem isOpen_pieceApexOne : IsOpen (pieceApexOne σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  filter_upwards [ev_gt' (contAt_norm' z) hz.1,
    ev_gt' (continuousAt_hd_of_disc h 0 hz.1) hz.2] with u a b
  exact ⟨a, b⟩

theorem isOpen_pieceApexTwo : IsOpen (pieceApexTwo σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  filter_upwards [ev_gt' (contAt_norm' z) hz.1,
    ev_gt' (continuousAt_hd_of_disc h 1 hz.1) hz.2] with u a b
  exact ⟨a, b⟩

omit h in
theorem isOpen_pieceOuter : IsOpen (pieceOuter σ) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem isOpen_pieceCornerOne : IsOpen (pieceCornerOne σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hz1, a1, a2, a3, a4, a5⟩ := hz
  filter_upwards [ev_gt' (contAt_norm' z) hz1,
    ev_lt' (continuousAt_hd_of_disc h 0 hz1) a1, ev_gt' (continuousAt_canon_of_disc h 0 hz1) a2,
    ev_lt' (continuousAt_hd_of_disc h 1 hz1) a3, ev_lt' (contAt_norm' z) a4,
    (isOpen_validOne h).mem_nhds a5] with u b0 b1 b2 b3 b4 b5
  exact ⟨b0, b1, b2, b3, b4, b5⟩

theorem isOpen_pieceCornerTwo : IsOpen (pieceCornerTwo σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hz1, a1, a2, a3, a4, a5, a6⟩ := hz
  filter_upwards [ev_gt' (contAt_norm' z) hz1,
    ev_lt' (continuousAt_hd_of_disc h 1 hz1) a1, ev_gt' (continuousAt_canon_of_disc h 1 hz1) a2,
    ev_lt' (continuousAt_hd_of_disc h 0 hz1) a3, ev_lt' (contAt_norm' z) a4,
    ev_lt' (continuousAt_canon_of_disc h 0 hz1) a5, (isOpen_validTwo h).mem_nhds a6]
    with u b0 b1 b2 b3 b4 b5 b6
  exact ⟨b0, b1, b2, b3, b4, b5, b6⟩

theorem isOpen_pieceLens : IsOpen (pieceLens σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hz1, a1, a2, a3, a4, a5⟩ := hz
  filter_upwards [ev_gt' (contAt_norm' z) hz1,
    ev_lt' (continuousAt_hd_of_disc h 0 hz1) a1, ev_lt' (continuousAt_hd_of_disc h 1 hz1) a2,
    ev_gt' (contDiffAt_lensCoord h hz1).continuousAt.abs a3,
    ev_lt' (contAt_norm' z) a4, (isOpen_validLens h).mem_nhds a5]
    with u b0 b1 b2 b3 b4 b5
  exact ⟨b0, b1, b2, b3, b4, b5⟩

theorem isOpen_pieceCornerThree : IsOpen (pieceCornerThree σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hz1, a1, a2, a3, a4, a5, a6, a7⟩ := hz
  filter_upwards [ev_gt' (contAt_norm' z) hz1,
    ev_lt' (continuousAt_canon_of_disc h 0 hz1) a1, ev_lt' (continuousAt_canon_of_disc h 1 hz1) a2,
    ev_lt' (contDiffAt_lensCoord h hz1).continuousAt.abs a3,
    ev_lt' (contAt_norm' z) a4, ev_lt' (continuousAt_hd_of_disc h 0 hz1) a5,
    ev_lt' (continuousAt_hd_of_disc h 1 hz1) a6, (isOpen_validThree h).mem_nhds a7]
    with u b0 b1 b2 b3 b4 b5 b6 b7
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩

theorem isOpen_pieceJunctionOne : IsOpen (pieceJunctionOne σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hz1, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hz
  filter_upwards [ev_gt' (contAt_norm' z) hz1,
    ev_lt' (continuousAt_hd_of_disc h 0 hz1) a1, ev_lt' (continuousAt_canon_of_disc h 1 hz1) a2,
    ev_lt' (contDiffAt_lensCoord h hz1).continuousAt a3, ev_lt' (contAt_norm' z) a4,
    ev_lt' (contAt_normAddRe_comp continuousAt_id) a5,
    ev_lt' (continuousAt_blendThree_of_disc h 1 _ hz1 a5) a6,
    ev_lt' (continuousAt_hd_of_disc h 1 hz1) a7, (isOpen_validJunctionOne h).mem_nhds a8]
    with u b0 b1 b2 b3 b4 b5 b6 b7 b8
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩

theorem isOpen_pieceJunctionTwo : IsOpen (pieceJunctionTwo σ) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hz1, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hz
  filter_upwards [ev_gt' (contAt_norm' z) hz1,
    ev_lt' (continuousAt_hd_of_disc h 1 hz1) a1, ev_lt' (continuousAt_canon_of_disc h 0 hz1) a2,
    ev_lt' (contDiffAt_lensCoord h hz1).continuousAt a3, ev_lt' (contAt_norm' z) a4,
    ev_lt' (contAt_normAddRe_comp continuousAt_id) a5,
    ev_gt' (continuousAt_blendThree_of_disc h 1 _ hz1 a5) a6,
    ev_lt' (continuousAt_hd_of_disc h 0 hz1) a7, (isOpen_validJunctionTwo h).mem_nhds a8]
    with u b0 b1 b2 b3 b4 b5 b6 b7 b8
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩

theorem isOpen_hypGoodSet : IsOpen (hypGoodSet σ) :=
  ((((((((isOpen_pieceApexOne h).union (isOpen_pieceApexTwo h)).union isOpen_pieceOuter).union
    (isOpen_pieceCornerOne h)).union (isOpen_pieceCornerTwo h)).union (isOpen_pieceLens h)).union
      (isOpen_pieceCornerThree h)).union (isOpen_pieceJunctionOne h)).union
        (isOpen_pieceJunctionTwo h)

theorem norm_lt_one_of_hypGoodSet {z : ℂ} (hz : z ∈ hypGoodSet σ) : ‖z‖ < 1 := by
  have hg3 : (hypLayout σ).g₃ < 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, a, b, c, d⟩ := hypLayout_params h
    linarith
  rcases hz with (((((((hz | hz) | hz) | hz) | hz) | hz) | hz) | hz) | hz
  · exact hz.1
  · exact hz.1
  · exact lt_trans hz.2 hg3
  · exact hz.1
  · exact hz.1
  · exact hz.1
  · exact hz.1
  · exact hz.1
  · exact hz.1

theorem hasDerivAt_rotOne_hyp {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt σ.rotOne (-exp (-((σ.θ₃ : ℂ) * I)) * ((1 - conj σ.vertexOne * σ.vertexOne) /
      (1 - conj σ.vertexOne * z) ^ 2)) z := by
  have e : σ.rotOne = fun u => -exp (-((σ.θ₃ : ℂ) * I)) * mob σ.vertexOne u :=
    funext (rotOne_eq_mul_mob h)
  rw [e]
  exact (hasDerivAt_mob (one_sub_conj_mul_ne_zero (norm_vertexOne_lt_one h) hz)).const_mul _

theorem hasDerivAt_rotTwo_hyp {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt σ.rotTwo (-exp ((σ.θ₂ : ℂ) * I) * ((1 - conj σ.vertexTwo * σ.vertexTwo) /
      (1 - conj σ.vertexTwo * z) ^ 2)) z := by
  have e : σ.rotTwo = fun u => -exp ((σ.θ₂ : ℂ) * I) * mob σ.vertexTwo u :=
    funext (rotTwo_eq_mul_mob h)
  rw [e]
  exact (hasDerivAt_mob (one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz)).const_mul _

theorem good_apexOne {z : ℂ} (hz : ‖z‖ < 1) :
    ContDiffAt ℝ ∞ (fun u => 3 / 2 + σ.rotOne u ^ σ.p₁ / 2) z ∧
      (z ≠ σ.vertexOne → 0 < (fderiv ℝ (fun u => 3 / 2 + σ.rotOne u ^ σ.p₁ / 2) z).det) := by
  refine ⟨contDiffAt_const.add (((contDiffAt_rotOne h hz).pow _).div_const _), fun hv => ?_⟩
  have hd : HasDerivAt (fun u => 3 / 2 + σ.rotOne u ^ σ.p₁ / 2)
      ((σ.p₁ : ℂ) * σ.rotOne z ^ (σ.p₁ - 1) * (-exp (-((σ.θ₃ : ℂ) * I)) *
        ((1 - conj σ.vertexOne * σ.vertexOne) / (1 - conj σ.vertexOne * z) ^ 2)) / 2) z := by
    exact (((hasDerivAt_rotOne_hyp h hz).pow σ.p₁).div_const 2).const_add (3 / 2)
  rw [det_fderiv_of_hasDerivAt hd]
  apply normSq_pos.2
  have hr := rotOne_ne_zero h hz hv
  have hp : (σ.p₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := σ.two_le_p₁; omega)
  have hD : (1 - conj σ.vertexOne * σ.vertexOne) / (1 - conj σ.vertexOne * z) ^ 2 ≠ 0 :=
    div_ne_zero (one_sub_conj_mul_self_ne_zero (normSq_vertexOne_ne_one h))
      (pow_ne_zero _ (one_sub_conj_mul_ne_zero (norm_vertexOne_lt_one h) hz))
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hp (pow_ne_zero _ hr))
    (mul_ne_zero (neg_ne_zero.2 (Complex.exp_ne_zero _)) hD)) two_ne_zero

theorem good_apexTwo {z : ℂ} (hz : ‖z‖ < 1) :
    ContDiffAt ℝ ∞ (fun u => -(3 / 2) + σ.rotTwo u ^ σ.p₂ / 2) z ∧
      (z ≠ σ.vertexTwo → 0 < (fderiv ℝ (fun u => -(3 / 2) + σ.rotTwo u ^ σ.p₂ / 2) z).det) := by
  refine ⟨contDiffAt_const.add (((contDiffAt_rotTwo h hz).pow _).div_const _), fun hv => ?_⟩
  have hd : HasDerivAt (fun u => -(3 / 2) + σ.rotTwo u ^ σ.p₂ / 2)
      ((σ.p₂ : ℂ) * σ.rotTwo z ^ (σ.p₂ - 1) * (-exp ((σ.θ₂ : ℂ) * I) *
        ((1 - conj σ.vertexTwo * σ.vertexTwo) / (1 - conj σ.vertexTwo * z) ^ 2)) / 2) z := by
    exact (((hasDerivAt_rotTwo_hyp h hz).pow σ.p₂).div_const 2).const_add (-(3 / 2))
  rw [det_fderiv_of_hasDerivAt hd]
  apply normSq_pos.2
  have hr : σ.rotTwo z ≠ 0 := by
    intro h0
    exact hv (rotTwo_injOn h hz (norm_vertexTwo_lt_one h) (by rw [h0, rotTwo_vertexTwo h]))
  have hp : (σ.p₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := σ.two_le_p₂; omega)
  have hD : (1 - conj σ.vertexTwo * σ.vertexTwo) / (1 - conj σ.vertexTwo * z) ^ 2 ≠ 0 :=
    div_ne_zero (one_sub_conj_mul_self_ne_zero (normSq_vertexTwo_ne_one h))
      (pow_ne_zero _ (one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz))
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hp (pow_ne_zero _ hr))
    (mul_ne_zero (neg_ne_zero.2 (Complex.exp_ne_zero _)) hD)) two_ne_zero

omit h in
theorem good_of_piece {s : Set ℂ} (hs : IsOpen s) {g : ℂ → ℂ}
    (heq : ∀ u ∈ s, hypPreFold σ (hypLayout σ) u = g u) {z : ℂ} (hz : z ∈ s)
    (hg : ContDiffAt ℝ ∞ g z) :
    ContDiffAt ℝ ∞ (hypPreFold σ (hypLayout σ)) z ∧
      (fderiv ℝ (hypPreFold σ (hypLayout σ)) z).det = (fderiv ℝ g z).det := by
  have hev : hypPreFold σ (hypLayout σ) =ᶠ[𝓝 z] g := Filter.eventually_of_mem (hs.mem_nhds hz) heq
  exact ⟨hg.congr_of_eventuallyEq hev, by rw [hev.fderiv_eq]⟩

theorem good_hypPreFold {z : ℂ} (hz : z ∈ hypGoodSet σ) :
    ContDiffAt ℝ ∞ (hypPreFold σ (hypLayout σ)) z ∧
      (z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ (hypPreFold σ (hypLayout σ)) z).det) := by
  rcases hz with (((((((hz | hz) | hz) | hz) | hz) | hz) | hz) | hz) | hz
  · obtain ⟨hs, hd⟩ := good_apexOne h hz.1
    obtain ⟨a, b⟩ := good_of_piece (isOpen_pieceApexOne h)
      (fun _ hu => hypPreFold_eq_apexOne hu) hz hs
    exact ⟨a, fun h1 _ => b ▸ hd h1⟩
  · obtain ⟨hs, hd⟩ := good_apexTwo h hz.1
    obtain ⟨a, b⟩ := good_of_piece (isOpen_pieceApexTwo h)
      (fun _ hu => hypPreFold_eq_apexTwo h hu) hz hs
    exact ⟨a, fun _ h2 => b ▸ hd h2⟩
  · have hz0 : z ≠ 0 := norm_pos_iff.1 hz.1
    obtain ⟨a, b⟩ := good_of_piece isOpen_pieceOuter (fun _ hu => hypPreFold_eq_outerPiece h hu)
      hz (contDiffAt_compactOuterGerm σ.p₃ hz0)
    refine ⟨a, fun _ _ => b ▸ det_fderiv_compactOuterGerm_pos (one_le_p₃ (σ := σ)) hz0 ?_⟩
    have hn : ‖z‖ < 1 := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, a, b, c, d⟩ := hypLayout_params h
      linarith [hz.2]
    calc ‖z‖ ^ σ.p₃ ≤ 1 := pow_le_one₀ (norm_nonneg _) hn.le
      _ < 7 := by norm_num
  · obtain ⟨a, b⟩ := good_of_piece (isOpen_pieceCornerOne h)
      (fun _ hu => hypPreFold_eq_cornerOne h hu) hz (contDiffAt_foldCornerOne h hz.2.2.2.2.2.1)
    exact ⟨a, fun _ _ => b ▸ hz.2.2.2.2.2.2⟩
  · obtain ⟨a, b⟩ := good_of_piece (isOpen_pieceCornerTwo h)
      (fun _ hu => hypPreFold_eq_cornerTwo h hu) hz
      (contDiffAt_foldCornerTwo h hz.2.2.2.2.2.2.1)
    exact ⟨a, fun _ _ => b ▸ hz.2.2.2.2.2.2.2⟩
  · obtain ⟨a, b⟩ := good_of_piece (isOpen_pieceLens h) (fun _ hu => hypPreFold_eq_lens h hu)
      hz (contDiffAt_bridgeTwo h hz.2.2.2.2.2.1)
    exact ⟨a, fun _ _ => b ▸ hz.2.2.2.2.2.2.2.2⟩
  · obtain ⟨a, b⟩ := good_of_piece (isOpen_pieceCornerThree h)
      (fun _ hu => hypPreFold_eq_cornerThree h hu) hz
      (contDiffAt_foldCornerThree h hz.2.2.2.2.2.2.2.1)
    exact ⟨a, fun _ _ => b ▸ hz.2.2.2.2.2.2.2.2⟩
  · obtain ⟨a, b⟩ := good_of_piece (isOpen_pieceJunctionOne h)
      (fun _ hu => hypPreFold_eq_junctionOne h hu) hz
      (contDiffAt_bridgeOne h hz.2.2.2.2.2.2.2.2.1)
    exact ⟨a, fun _ _ => b ▸ hz.2.2.2.2.2.2.2.2.2.2.2⟩
  · obtain ⟨a, b⟩ := good_of_piece (isOpen_pieceJunctionTwo h)
      (fun _ hu => hypPreFold_eq_junctionTwo h hu) hz
      (contDiffAt_bridgeZero h hz.2.2.2.2.2.2.2.2.1)
    exact ⟨a, fun _ _ => b ▸ hz.2.2.2.2.2.2.2.2.2.2.2⟩

end Hyp

end HypFold

end GC.Seifert
