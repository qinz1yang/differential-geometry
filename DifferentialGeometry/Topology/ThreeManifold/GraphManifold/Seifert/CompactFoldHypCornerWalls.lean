import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypCorners

/-!
# Wall identities and angle orders of the hyperbolic corners

Lane CF-H, tier 2 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`, §4, curvature `-1`).
In the rotated disc coordinates the reflections through a vertex are `ω ↦ ω̄` and
`ω ↦ e^{2iθ} ω̄` (`rotOne_refl_one`, `rotOne_refl_two`, `rotTwo_refl_zero` and
`rotTwo_refl_two` of `CompactFoldHypTriangle`), so the apex angles are odd about their wall value
(`psiOne_refl_one`, `psiOne_refl_two`, …). The moduli are reflection invariant
(`modOne_refl_one`, …) and the bridges reflection equivariant, hence the bridge angles are odd
about `0` or `π` (`angleOneAtOne_refl_one`, `angleTwoAtOne_refl_two`, …). Where the angular
weight of a corner takes the same saturated value at a point and at its mirror image, the corner
satisfies `corner ∘ refl = conj ∘ corner` (`cornerOne_refl_one`, `cornerOne_refl_two`,
`cornerTwo_refl_two`, `cornerTwo_refl_zero`, `cornerThree_refl_zero`, `cornerThree_refl_one`).

The bridge angles about each centre are ordered on the closed side of the walls
(`angleOneAtOne_le_angleTwoAtOne`, `angleTwoAtTwo_le_angleZeroAtTwo`,
`angleOneAtThree_le_angleZeroAtThree`), because `Re bridgeOne > 3/2 > |Re bridgeTwo|` and
`Re bridgeZero < -3/2` on the disc.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

theorem discAngle_conj' (w : ℂ) : discAngle (conj w) = -discAngle w := by
  simp only [discAngle, Complex.norm_conj, conj_re, conj_im, halfArg_neg]

theorem discAngle_exp_mul_conj' {w : ℂ} (h : 0 < ‖w‖ + w.re) {θ : ℝ}
    (h1 : -Real.pi < θ - discAngle w) (h2 : θ - discAngle w < Real.pi) :
    discAngle (exp ((θ : ℂ) * I) * conj w) = θ - discAngle w := by
  have hc : 0 < ‖conj w‖ + (conj w).re := by rwa [Complex.norm_conj, conj_re]
  have hc0 : conj w ≠ 0 := by
    intro h0
    rw [h0] at hc
    simp at hc
  rw [mul_comm, discAngle_mul_exp hc0 hc
    (by rw [discAngle_conj']; linarith) (by rw [discAngle_conj']; linarith), discAngle_conj']
  ring

theorem two_mul_ofReal_mul_I' (θ : ℝ) : 2 * (θ : ℂ) * I = ((2 * θ : ℝ) : ℂ) * I := by
  push_cast
  ring

theorem conj_polar' (c S Θ : ℝ) :
    conj ((c : ℂ) + (S : ℂ) * exp ((Θ : ℂ) * I)) =
      (c : ℂ) + (S : ℂ) * exp (((-Θ : ℝ) : ℂ) * I) := by
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 3
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem exp_two_pi_sub' (Θ : ℝ) :
    exp (((2 * Real.pi - Θ : ℝ) : ℂ) * I) = exp (((-Θ : ℝ) : ℂ) * I) := by
  rw [show ((2 * Real.pi - Θ : ℝ) : ℂ) * I = ((-Θ : ℝ) : ℂ) * I + 2 * Real.pi * I by
    push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem halfArg_mem_Ico' {S R J : ℝ} (hSR : 0 < S + R) (hJ : 0 ≤ J) :
    0 ≤ halfArg S R J ∧ halfArg S R J < Real.pi := by
  unfold halfArg
  have h1 := Real.arctan_lt_pi_div_two (J / (S + R))
  have h2 : 0 ≤ Real.arctan (J / (S + R)) := Real.arctan_nonneg.2 (div_nonneg hJ hSR.le)
  constructor <;> linarith

theorem negHalfArg_mem_Ioc' {S R J : ℝ} (hSR : 0 < S - R) (hJ : 0 ≤ J) :
    0 < negHalfArg S R J ∧ negHalfArg S R J ≤ Real.pi := by
  unfold negHalfArg
  have h1 := Real.arctan_lt_pi_div_two (J / (S - R))
  have h2 : 0 ≤ Real.arctan (J / (S - R)) := Real.arctan_nonneg.2 (div_nonneg hJ hSR.le)
  constructor <;> linarith

theorem halfArg_le_negHalfArg' {S R J R' J' : ℝ} (hS : 0 < S) (hSR : 0 < S + R)
    (hSR' : 0 < S - R') (hh : R ^ 2 + J ^ 2 = S ^ 2) (hh' : R' ^ 2 + J' ^ 2 = S ^ 2)
    (hJ : 0 ≤ J) (hJ' : 0 ≤ J') (hRR : R' ≤ R) : halfArg S R J ≤ negHalfArg S R' J' := by
  obtain ⟨a0, a1⟩ := halfArg_mem_Ico' hSR hJ
  obtain ⟨b0, b1⟩ := negHalfArg_mem_Ioc' hSR' hJ'
  by_contra hc
  have hlt : negHalfArg S R' J' < halfArg S R J := not_le.1 hc
  have := Real.cos_lt_cos_of_nonneg_of_le_pi b0.le a1.le hlt
  rw [halfArg_cos hS hSR hh, negHalfArg_cos hS hSR' hh'] at this
  rw [div_lt_div_iff_of_pos_right hS] at this
  linarith

theorem sq_of_norm_sub {u : ℂ} {c S : ℝ} (hn : ‖u - c‖ = S) :
    (u.re - c) ^ 2 + u.im ^ 2 = S ^ 2 := by
  rw [← hn, Complex.sq_norm, normSq_apply]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
  ring

theorem im_twoCircle_nonneg {a b A B w P : ℝ} (hw : 0 ≤ w) :
    0 ≤ (twoCircle a b A B w P).im := by
  rw [twoCircle_im]
  have := Real.sqrt_nonneg P
  have := abs_nonneg (b - a)
  positivity

variable {σ : CompactShape}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem rotTwo_refl_zero (z : ℂ) :
    σ.rotTwo (σ.refl 0 z) = exp (2 * (σ.θ₂ : ℂ) * I) * conj (σ.rotTwo z) := by
  change σ.rotTwo (conj z) = _
  have e : mob σ.vertexTwo (conj z) = conj (mob σ.vertexTwo z) := by
    rw [vertexTwo_eq, ← mob_conj_conj, Complex.conj_ofReal]
  rw [rotTwo_eq_mul_mob h, rotTwo_eq_mul_mob h, e, map_mul, map_neg, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [show -exp ((σ.θ₂ : ℂ) * I) * conj (mob σ.vertexTwo z) =
      exp (2 * (σ.θ₂ : ℂ) * I) * (-exp ((σ.θ₂ : ℂ) * -I) * conj (mob σ.vertexTwo z)) by
    rw [← mul_assoc, mul_neg, ← Complex.exp_add]
    ring_nf]

theorem rotOne_refl_one (z : ℂ) : σ.rotOne (σ.refl 1 z) = conj (σ.rotOne z) := by
  change σ.rotOne (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) = _
  set u := exp ((σ.θ₃ : ℂ) * I) with hu
  have hu1 : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hv : σ.vertexOne = u * (sideOneThree σ : ℂ) := by rw [vertexOne_eq, mul_comm]
  have hcu : conj u = exp (-((σ.θ₃ : ℂ) * I)) := by
    rw [hu, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have e1 : exp (2 * (σ.θ₃ : ℂ) * I) * conj z = u * conj (exp (-((σ.θ₃ : ℂ) * I)) * z) := by
    rw [map_mul, ← hcu, Complex.conj_conj, ← mul_assoc, hu, ← Complex.exp_add]
    ring_nf
  have e2 : z = u * (exp (-((σ.θ₃ : ℂ) * I)) * z) := by
    rw [← mul_assoc, hu, exp_mul_exp_neg, one_mul]
  have hc : mob (sideOneThree σ : ℂ) (conj (exp (-((σ.θ₃ : ℂ) * I)) * z)) =
      conj (mob (sideOneThree σ : ℂ) (exp (-((σ.θ₃ : ℂ) * I)) * z)) := by
    rw [← mob_conj_conj, Complex.conj_ofReal]
  rw [rotOne_eq_mul_mob h, rotOne_eq_mul_mob h, hv, e1, mob_mul_mul hu1, hc]
  conv_rhs => rw [e2, mob_mul_mul hu1]
  rw [map_mul, map_mul, ← hcu, map_neg, Complex.conj_conj]
  ring

theorem rotOne_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    σ.rotOne (σ.refl 2 z) = exp (2 * (σ.θ₁ : ℂ) * I) * conj (σ.rotOne z) := by
  rw [rotOne_eq_mob_rotTwo h (norm_refl_lt_one h 2 hz), rotTwo_refl_two h hz,
    rotOne_eq_mob_rotTwo h hz]
  have hc : mob (sideOneTwo σ : ℂ) (conj (σ.rotTwo z)) =
      conj (mob (sideOneTwo σ : ℂ) (σ.rotTwo z)) := by
    rw [← mob_conj_conj, Complex.conj_ofReal]
  rw [hc, map_mul, map_neg, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [show exp (2 * (σ.θ₁ : ℂ) * I) * (-exp ((σ.θ₁ : ℂ) * -I) *
      conj (mob (sideOneTwo σ : ℂ) (σ.rotTwo z))) =
      -(exp (2 * (σ.θ₁ : ℂ) * I) * exp ((σ.θ₁ : ℂ) * -I)) *
        conj (mob (sideOneTwo σ : ℂ) (σ.rotTwo z)) by ring, ← Complex.exp_add]
  ring_nf

theorem psiOne_refl_one (z : ℂ) : psiOne σ (σ.refl 1 z) = -psiOne σ z := by
  rw [psiOne, rotOne_refl_one h, discAngle_conj', psiOne]

theorem psiOne_refl_two {z : ℂ} (hz : ‖z‖ < 1) (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (h1 : -Real.pi < 2 * σ.θ₁ - psiOne σ z) (h2 : 2 * σ.θ₁ - psiOne σ z < Real.pi) :
    psiOne σ (σ.refl 2 z) = 2 * σ.θ₁ - psiOne σ z := by
  rw [psiOne, rotOne_refl_two h hz, two_mul_ofReal_mul_I']
  exact discAngle_exp_mul_conj' hψ h1 h2

theorem psiTwo_refl_two {z : ℂ} (hz : ‖z‖ < 1) : psiTwo σ (σ.refl 2 z) = -psiTwo σ z := by
  rw [psiTwo, rotTwo_refl_two h hz, discAngle_conj', psiTwo]

theorem psiTwo_refl_zero {z : ℂ} (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (h1 : -Real.pi < 2 * σ.θ₂ - psiTwo σ z) (h2 : 2 * σ.θ₂ - psiTwo σ z < Real.pi) :
    psiTwo σ (σ.refl 0 z) = 2 * σ.θ₂ - psiTwo σ z := by
  rw [psiTwo, rotTwo_refl_zero h, two_mul_ofReal_mul_I']
  exact discAngle_exp_mul_conj' hψ h1 h2

omit h in
theorem psiThree_refl_zero (z : ℂ) : discAngle (σ.refl 0 z) = -discAngle z :=
  discAngle_conj' z

omit h in
theorem psiThree_refl_one {z : ℂ} (hψ : 0 < ‖z‖ + z.re)
    (h1 : -Real.pi < 2 * σ.θ₃ - discAngle z) (h2 : 2 * σ.θ₃ - discAngle z < Real.pi) :
    discAngle (σ.refl 1 z) = 2 * σ.θ₃ - discAngle z := by
  change discAngle (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) = _
  rw [two_mul_ofReal_mul_I']
  exact discAngle_exp_mul_conj' hψ h1 h2

theorem modOne_refl_one (z : ℂ) : modOne σ (σ.refl 1 z) = modOne σ z := by
  rw [modOne, modOne, canon_eq_of_hd (hd_refl_one_zero h z)]

theorem modOne_refl_two {z : ℂ} (hz : ‖z‖ < 1) : modOne σ (σ.refl 2 z) = modOne σ z := by
  rw [modOne, modOne, canon_eq_of_hd (hd_refl_two_zero h hz)]

theorem modTwo_refl_two {z : ℂ} (hz : ‖z‖ < 1) : modTwo σ (σ.refl 2 z) = modTwo σ z := by
  rw [modTwo, modTwo, canon_eq_of_hd (hd_refl_two_one h hz)]

theorem modTwo_refl_zero (z : ℂ) : modTwo σ (σ.refl 0 z) = modTwo σ z := by
  rw [modTwo, modTwo, canon_eq_of_hd (hd_refl_zero_one h z)]

theorem modThree_refl_zero (z : ℂ) : modThree σ (σ.refl 0 z) = modThree σ z := by
  rw [modThree, modThree, canon_eq_of_hd (hd_refl_zero_two h z)]

theorem modThree_refl_one (z : ℂ) : modThree σ (σ.refl 1 z) = modThree σ z := by
  rw [modThree, modThree, canon_eq_of_hd (hd_refl_one_two h z)]

theorem angleOneAtOne_refl_one (z : ℂ) :
    angleOneAtOne σ (σ.refl 1 z) = -angleOneAtOne σ z := by
  rw [angleOneAtOne, angleOneAtOne, modOne_refl_one h, bridgeOne_refl_one h, conj_re, conj_im,
    halfArg_neg]

theorem angleOneAtThree_refl_one (z : ℂ) :
    angleOneAtThree σ (σ.refl 1 z) = -angleOneAtThree σ z := by
  rw [angleOneAtThree, angleOneAtThree, modThree_refl_one h, bridgeOne_refl_one h, conj_re,
    conj_im, halfArg_neg]

theorem angleTwoAtOne_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    angleTwoAtOne σ (σ.refl 2 z) = 2 * Real.pi - angleTwoAtOne σ z := by
  rw [angleTwoAtOne, angleTwoAtOne, modOne_refl_two h hz, bridgeTwo_refl_two h hz, conj_re,
    conj_im, negHalfArg_neg]

theorem angleTwoAtTwo_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    angleTwoAtTwo σ (σ.refl 2 z) = -angleTwoAtTwo σ z := by
  rw [angleTwoAtTwo, angleTwoAtTwo, modTwo_refl_two h hz, bridgeTwo_refl_two h hz, conj_re,
    conj_im, halfArg_neg]

theorem angleZeroAtTwo_refl_zero (z : ℂ) :
    angleZeroAtTwo σ (σ.refl 0 z) = 2 * Real.pi - angleZeroAtTwo σ z := by
  rw [angleZeroAtTwo, angleZeroAtTwo, modTwo_refl_zero h, bridgeZero_refl_zero h, conj_re,
    conj_im, negHalfArg_neg]

theorem angleZeroAtThree_refl_zero (z : ℂ) :
    angleZeroAtThree σ (σ.refl 0 z) = 2 * Real.pi - angleZeroAtThree σ z := by
  rw [angleZeroAtThree, angleZeroAtThree, modThree_refl_zero h, bridgeZero_refl_zero h, conj_re,
    conj_im, negHalfArg_neg]

theorem cornerOne_refl_one (a b β β' : ℝ) {z : ℂ}
    (hc : coneStep a b (hd σ 0 z) = 0 ∨
      (lensSwitch σ β β' z = 1 ∧ lensSwitch σ β β' (σ.refl 1 z) = 1)) :
    cornerOne σ a b β β' (σ.refl 1 z) = conj (cornerOne σ a b β β' z) := by
  have hn : hd σ 0 (σ.refl 1 z) = hd σ 0 z := hd_refl_one_zero h z
  have hΘ : angleCornerOne σ a b β β' (σ.refl 1 z) = -angleCornerOne σ a b β β' z := by
    rw [angleCornerOne, angleCornerOne, hn, psiOne_refl_one h, angleOneAtOne_refl_one h]
    rcases hc with hc | ⟨h1, h2⟩
    · rw [hc]
      ring
    · rw [h1, h2]
      ring
  rw [cornerOne, cornerOne, hn, hΘ, conj_polar']

theorem cornerOne_refl_two (a b β β' : ℝ) {z : ℂ} (hz : ‖z‖ < 1)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (h1 : -Real.pi < 2 * σ.θ₁ - psiOne σ z) (h2 : 2 * σ.θ₁ - psiOne σ z < Real.pi)
    (hc : coneStep a b (hd σ 0 z) = 0 ∨
      (lensSwitch σ β β' z = 0 ∧ lensSwitch σ β β' (σ.refl 2 z) = 0)) :
    cornerOne σ a b β β' (σ.refl 2 z) = conj (cornerOne σ a b β β' z) := by
  have hn : hd σ 0 (σ.refl 2 z) = hd σ 0 z := hd_refl_two_zero h hz
  have hp : (σ.p₁ : ℝ) * σ.θ₁ = Real.pi := by rw [mul_comm]; exact θ₁_mul σ
  have hΘ : angleCornerOne σ a b β β' (σ.refl 2 z) =
      2 * Real.pi - angleCornerOne σ a b β β' z := by
    rw [angleCornerOne, angleCornerOne, hn, psiOne_refl_two h hz hψ h1 h2,
      angleTwoAtOne_refl_two h hz]
    rcases hc with hc | ⟨h3, h4⟩
    · rw [hc]
      linear_combination 2 * hp
    · rw [h3, h4]
      linear_combination 2 * (1 - coneStep a b (hd σ 0 z)) * hp
  rw [cornerOne, cornerOne, hn, hΘ, exp_two_pi_sub', conj_polar']

theorem cornerTwo_refl_two (a b β β' : ℝ) {z : ℂ} (hz : ‖z‖ < 1)
    (hc : coneStep a b (hd σ 1 z) = 0 ∨
      (lensSwitch σ β β' z = 0 ∧ lensSwitch σ β β' (σ.refl 2 z) = 0)) :
    cornerTwo σ a b β β' (σ.refl 2 z) = conj (cornerTwo σ a b β β' z) := by
  have hn : hd σ 1 (σ.refl 2 z) = hd σ 1 z := hd_refl_two_one h hz
  have hΘ : angleCornerTwo σ a b β β' (σ.refl 2 z) = -angleCornerTwo σ a b β β' z := by
    rw [angleCornerTwo, angleCornerTwo, hn, psiTwo_refl_two h hz, angleTwoAtTwo_refl_two h hz]
    rcases hc with hc | ⟨h1, h2⟩
    · rw [hc]
      ring
    · rw [h1, h2]
      ring
  rw [cornerTwo, cornerTwo, hn, hΘ, conj_polar']

theorem cornerTwo_refl_zero (a b β β' : ℝ) {z : ℂ}
    (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (h1 : -Real.pi < 2 * σ.θ₂ - psiTwo σ z) (h2 : 2 * σ.θ₂ - psiTwo σ z < Real.pi)
    (hc : coneStep a b (hd σ 1 z) = 0 ∨
      (lensSwitch σ β β' z = 1 ∧ lensSwitch σ β β' (σ.refl 0 z) = 1)) :
    cornerTwo σ a b β β' (σ.refl 0 z) = conj (cornerTwo σ a b β β' z) := by
  have hn : hd σ 1 (σ.refl 0 z) = hd σ 1 z := hd_refl_zero_one h z
  have hp : (σ.p₂ : ℝ) * σ.θ₂ = Real.pi := by rw [mul_comm]; exact θ₂_mul σ
  have hΘ : angleCornerTwo σ a b β β' (σ.refl 0 z) =
      2 * Real.pi - angleCornerTwo σ a b β β' z := by
    rw [angleCornerTwo, angleCornerTwo, hn, psiTwo_refl_zero h hψ h1 h2,
      angleZeroAtTwo_refl_zero h]
    rcases hc with hc | ⟨h3, h4⟩
    · rw [hc]
      linear_combination 2 * hp
    · rw [h3, h4]
      linear_combination 2 * (1 - coneStep a b (hd σ 1 z)) * hp
  rw [cornerTwo, cornerTwo, hn, hΘ, exp_two_pi_sub', conj_polar']

theorem cornerThree_refl_zero (a b w δ : ℝ) {z : ℂ}
    (hc : coneStep a b ‖z‖ = 0 ∨ (nuThree σ w δ z = 0 ∧ nuThree σ w δ (σ.refl 0 z) = 0)) :
    cornerThree σ a b w δ (σ.refl 0 z) = conj (cornerThree σ a b w δ z) := by
  have hn : ‖σ.refl 0 z‖ = ‖z‖ := Complex.norm_conj z
  have hΘ : angleCornerThree σ a b w δ (σ.refl 0 z) =
      2 * Real.pi - angleCornerThree σ a b w δ z := by
    rw [angleCornerThree, angleCornerThree, hn, psiThree_refl_zero,
      angleZeroAtThree_refl_zero h]
    rcases hc with hc | ⟨h1, h2⟩
    · rw [hc]
      ring
    · rw [h1, h2]
      ring
  rw [cornerThree, cornerThree, hn, hΘ, exp_two_pi_sub', conj_polar']

theorem cornerThree_refl_one (a b w δ : ℝ) {z : ℂ} (hψ : 0 < ‖z‖ + z.re)
    (h1 : -Real.pi < 2 * σ.θ₃ - discAngle z) (h2 : 2 * σ.θ₃ - discAngle z < Real.pi)
    (hc : coneStep a b ‖z‖ = 0 ∨ (nuThree σ w δ z = 1 ∧ nuThree σ w δ (σ.refl 1 z) = 1)) :
    cornerThree σ a b w δ (σ.refl 1 z) = conj (cornerThree σ a b w δ z) := by
  have hn : ‖σ.refl 1 z‖ = ‖z‖ := by
    change ‖exp (2 * (σ.θ₃ : ℂ) * I) * conj z‖ = ‖z‖
    rw [norm_mul, norm_exp_two, one_mul, Complex.norm_conj]
  have hp : (σ.p₃ : ℝ) * σ.θ₃ = Real.pi := by rw [mul_comm]; exact θ₃_mul σ
  have hΘ : angleCornerThree σ a b w δ (σ.refl 1 z) = -angleCornerThree σ a b w δ z := by
    rw [angleCornerThree, angleCornerThree, hn, psiThree_refl_one hψ h1 h2,
      angleOneAtThree_refl_one h]
    rcases hc with hc | ⟨h3, h4⟩
    · rw [hc]
      linear_combination (-2) * hp
    · rw [h3, h4]
      linear_combination (-2) * (1 - coneStep a b ‖z‖) * hp
  rw [cornerThree, cornerThree, hn, hΘ, conj_polar']

theorem three_halves_lt_re_bridgeOne {z : ℂ} (hz : ‖z‖ < 1) :
    3 / 2 < (bridgeOne σ z).re := by
  have hA := modThree_mem h hz
  have hB := modOne_mem h hz
  rw [bridgeOne, twoCircle_re]
  have : 9 / 2 < modThree σ z ^ 2 - modOne σ z ^ 2 + (3 / 2 - 0) ^ 2 := by nlinarith
  have h2 : (3 / 2 : ℝ) * (2 * (3 / 2 - 0)) <
      modThree σ z ^ 2 - modOne σ z ^ 2 + (3 / 2 - 0) ^ 2 := by nlinarith
  have := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2 * (3 / 2 - 0))).2 h2
  linarith

theorem re_bridgeZero_lt {z : ℂ} (hz : ‖z‖ < 1) : (bridgeZero σ z).re < -(3 / 2) := by
  have hA := modThree_mem h hz
  have hB := modTwo_mem h hz
  rw [bridgeZero, twoCircle_re]
  have h2 : (3 / 2 : ℝ) * 3 < modThree σ z ^ 2 - modTwo σ z ^ 2 + (-(3 / 2) - 0) ^ 2 := by
    nlinarith
  have e : (modThree σ z ^ 2 - modTwo σ z ^ 2 + (-(3 / 2) - 0) ^ 2) / (2 * (-(3 / 2) - 0)) =
      -((modThree σ z ^ 2 - modTwo σ z ^ 2 + (-(3 / 2) - 0) ^ 2) / 3) := by ring
  rw [e]
  have := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2 h2
  linarith

theorem abs_re_bridgeTwo_lt {z : ℂ} (hz : z ∈ domOneTwo σ) : |(bridgeTwo σ z).re| < 3 / 2 :=
  lt_of_le_of_lt (Complex.abs_re_le_norm _) (norm_bridgeTwo_lt h hz)

theorem angleOneAtOne_le_angleTwoAtOne {z : ℂ} (hz1 : z ∈ domOneThree σ)
    (hz2 : z ∈ domOneTwo σ) (hpos1 : 0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2))
    (hpos2 : 0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2))
    (hw1 : 0 ≤ σ.wallSide 1 z) (hw2 : 0 ≤ sideTwo σ z) :
    angleOneAtOne σ z ≤ angleTwoAtOne σ z := by
  have hz := norm_lt_one_of_domOneThree hz1
  have hn1 : ‖bridgeOne σ z - ((3 / 2 : ℝ) : ℂ)‖ = modOne σ z := by
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring]; exact (norm_bridgeOne h hz1).2
  have hn2 : ‖bridgeTwo σ z - ((3 / 2 : ℝ) : ℂ)‖ = modOne σ z := by
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring]; exact (norm_bridgeTwo h hz2).1
  have hr1 := three_halves_lt_re_bridgeOne h hz
  have hr2 := abs_lt.1 (abs_re_bridgeTwo_lt h hz2)
  exact halfArg_le_negHalfArg' (by linarith [(modOne_mem h hz).1]) hpos1 hpos2
    (sq_of_norm_sub hn1) (sq_of_norm_sub hn2) (im_twoCircle_nonneg hw1)
    (im_twoCircle_nonneg hw2) (by linarith)

theorem angleTwoAtTwo_le_angleZeroAtTwo {z : ℂ} (hz2 : z ∈ domOneTwo σ)
    (hz0 : z ∈ domZeroThree σ) (hpos2 : 0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2))
    (hpos0 : 0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2))
    (hw2 : 0 ≤ sideTwo σ z) (hw0 : 0 ≤ σ.wallSide 0 z) :
    angleTwoAtTwo σ z ≤ angleZeroAtTwo σ z := by
  have hz := norm_lt_one_of_domOneTwo hz2
  have hn2 : ‖bridgeTwo σ z - ((-(3 / 2) : ℝ) : ℂ)‖ = modTwo σ z := by
    rw [show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add]
    exact (norm_bridgeTwo h hz2).2
  have hn0 : ‖bridgeZero σ z - ((-(3 / 2) : ℝ) : ℂ)‖ = modTwo σ z := by
    rw [show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add]
    exact (norm_bridgeZero h hz0).2
  have hr0 := re_bridgeZero_lt h hz
  have hr2 := abs_lt.1 (abs_re_bridgeTwo_lt h hz2)
  have := halfArg_le_negHalfArg' (by linarith [(modTwo_mem h hz).1])
    (by rw [sub_neg_eq_add]; exact hpos2) (by rw [sub_neg_eq_add]; exact hpos0)
    (sq_of_norm_sub hn2) (sq_of_norm_sub hn0) (im_twoCircle_nonneg hw2)
    (im_twoCircle_nonneg hw0) (by linarith)
  rw [sub_neg_eq_add, sub_neg_eq_add] at this
  exact this

theorem angleOneAtThree_le_angleZeroAtThree {z : ℂ} (hz1 : z ∈ domOneThree σ)
    (hz0 : z ∈ domZeroThree σ) (hpos1 : 0 < modThree σ z + (bridgeOne σ z).re)
    (hpos0 : 0 < modThree σ z - (bridgeZero σ z).re)
    (hw1 : 0 ≤ σ.wallSide 1 z) (hw0 : 0 ≤ σ.wallSide 0 z) :
    angleOneAtThree σ z ≤ angleZeroAtThree σ z := by
  have hz := norm_lt_one_of_domOneThree hz1
  have hn1 : ‖bridgeOne σ z - ((0 : ℝ) : ℂ)‖ = modThree σ z := by
    rw [ofReal_zero, sub_zero]; exact (norm_bridgeOne h hz1).1
  have hn0 : ‖bridgeZero σ z - ((0 : ℝ) : ℂ)‖ = modThree σ z := by
    rw [ofReal_zero, sub_zero]; exact (norm_bridgeZero h hz0).1
  have hr1 := re_bridgeOne_pos h hz
  have hr0 := re_bridgeZero_neg h hz
  have := halfArg_le_negHalfArg' (by linarith [(modThree_mem h hz).1])
    (by rw [sub_zero]; exact hpos1) (by rw [sub_zero]; exact hpos0)
    (sq_of_norm_sub hn1) (sq_of_norm_sub hn0) (im_twoCircle_nonneg hw1)
    (im_twoCircle_nonneg hw0) (by linarith)
  rw [sub_zero, sub_zero] at this
  exact this

end Hyp

end HypFold

end GC.Seifert
