import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypTriangle

/-!
# Canonical radii and the bracket factorisation of the hyperbolic compact triangle

Lane CF-H, tier 1 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`, §2, curvature `-1`).
Half-distance tangents add by `oplus a b = (a + b)/(1 + a b)`, which the Cayley ratio
`cay t = (1 + t)/(1 - t)` turns into a product (`cay_mul_cay`, inverse `uncay`, `oplus_uncay`).
The canonical radii (incircle tangent lengths) have half-tangents
`radTan a b c = uncay √(cay a · cay b / cay c)` (`tauOne`, `tauTwo`, `tauThree`), positive by the
strict triangle inequalities of `CompactFoldHypShape` and adding up to the side tangents:
`τ₁ ⊕ τ₃ = t₁₃`, `τ₂ ⊕ τ₃ = t₂₃`, `τ₁ ⊕ τ₂ = t₁₂` (`oplus_tauOne_tauThree`, …).

With the pseudo-hyperbolic distances `hd j z = ‖mob vⱼ z‖` (`v₃ = 0`) the canonical coordinates are
`canon j = (hd j - τⱼ)/(1 - hd j · τⱼ) = tanh ((dⱼ - rⱼ)/2)`, of absolute value `< 1` on the disc
(`abs_canon_lt_one`). The sum over the two vertices of a wall factorises exactly:
`canon i + canon j = (1 + τᵢτⱼ)/((1 - ϖᵢτᵢ)(1 - ϖⱼτⱼ)) · (ϖᵢ + ϖⱼ - t(1 + ϖᵢϖⱼ))` and, in a disc
coordinate `W = X + iY` with the two vertices at `0` and `t`, the bracket is
`Y² · bracketCof` (`bracket_identity_real`), the cofactor being positive on `pairDom t`, the disc
minus the two real rays beyond the vertices (`bracketCof_pos`, `mem_pairDom`). For the three walls
(`W = z`, `e^{-iθ₃} z`, `rotTwo z`) this gives `canon 1 + canon 2 = wallSide 0 ² · cofZeroThree`,
`canon 0 + canon 2 = wallSide 1 ² · cofOneThree`, `canon 0 + canon 1 = wallSide 2 ² · cofOneTwo`
with positive cofactors on the domains `domZeroThree`, `domOneThree`, `domOneTwo`.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GC.Seifert

namespace HypFold

def cay (t : ℝ) : ℝ := (1 + t) / (1 - t)

def uncay (q : ℝ) : ℝ := (q - 1) / (q + 1)

theorem cay_pos {t : ℝ} (h0 : -1 < t) (h1 : t < 1) : 0 < cay t :=
  div_pos (by linarith) (by linarith)

theorem uncay_cay {t : ℝ} (h1 : t < 1) : uncay (cay t) = t := by
  have h : (1 : ℝ) - t ≠ 0 := by linarith
  unfold uncay cay
  rw [div_sub_one h, div_add_one h, div_div_div_cancel_right₀ h]
  rw [div_eq_iff (by linarith)]
  ring

theorem uncay_lt_one {q : ℝ} (hq : 0 < q) : uncay q < 1 := by
  unfold uncay
  rw [div_lt_one (by linarith)]
  linarith

theorem neg_one_lt_uncay {q : ℝ} (hq : 0 < q) : -1 < uncay q := by
  unfold uncay
  rw [lt_div_iff₀ (by linarith)]
  linarith

theorem uncay_pos {q : ℝ} (hq : 1 < q) : 0 < uncay q :=
  div_pos (by linarith) (by linarith)

theorem oplus_uncay {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    oplus (uncay p) (uncay q) = uncay (p * q) := by
  unfold oplus uncay
  have h1 : p + 1 ≠ 0 := by linarith
  have h2 : q + 1 ≠ 0 := by linarith
  have h3 : 0 < p * q := mul_pos hp hq
  have h4 : 1 + (p - 1) / (p + 1) * ((q - 1) / (q + 1)) =
      2 * (p * q + 1) / ((p + 1) * (q + 1)) := by
    field_simp
    ring
  rw [h4, div_add_div _ _ h1 h2, div_div_div_cancel_right₀ (mul_ne_zero h1 h2),
    div_eq_div_iff (by positivity) (by linarith)]
  ring

theorem cay_mul_cay {a b : ℝ} (ha0 : -1 < a) (ha1 : a < 1) (hb0 : -1 < b) (hb1 : b < 1) :
    cay a * cay b = cay (oplus a b) := by
  have hab : 0 < 1 + a * b := by nlinarith
  unfold cay oplus
  have e1 : 1 + (a + b) / (1 + a * b) = (1 + a) * (1 + b) / (1 + a * b) := by
    field_simp
    ring
  have e2 : 1 - (a + b) / (1 + a * b) = (1 - a) * (1 - b) / (1 + a * b) := by
    field_simp
    ring
  rw [e1, e2, div_div_div_cancel_right₀ hab.ne', div_mul_div_comm]

theorem cay_lt_cay {a b : ℝ} (hb : b < 1) (hab : a < b) : cay a < cay b := by
  unfold cay
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

def radTan (a b c : ℝ) : ℝ := uncay (Real.sqrt (cay a * cay b / cay c))

theorem radTan_comm (a b c : ℝ) : radTan a b c = radTan b a c := by
  rw [radTan, radTan, mul_comm (cay a)]

theorem oplus_radTan {a b c : ℝ} (ha0 : -1 < a) (ha1 : a < 1) (hb0 : -1 < b) (hb1 : b < 1)
    (hc0 : -1 < c) (hc1 : c < 1) : oplus (radTan a b c) (radTan a c b) = a := by
  have pa := cay_pos ha0 ha1
  have pb := cay_pos hb0 hb1
  have pc := cay_pos hc0 hc1
  rw [radTan, radTan, oplus_uncay (Real.sqrt_pos.2 (by positivity))
    (Real.sqrt_pos.2 (by positivity)), ← Real.sqrt_mul (by positivity)]
  have e : cay a * cay b / cay c * (cay a * cay c / cay b) = cay a ^ 2 := by
    field_simp
  rw [e, Real.sqrt_sq pa.le, uncay_cay ha1]

theorem radTan_lt_one (a b c : ℝ) : radTan a b c < 1 := by
  unfold radTan uncay
  have h := Real.sqrt_nonneg (cay a * cay b / cay c)
  rw [div_lt_one (by linarith)]
  linarith

theorem radTan_pos {a b c : ℝ} (ha0 : -1 < a) (ha1 : a < 1) (hb0 : -1 < b) (hb1 : b < 1)
    (hc0 : -1 < c) (hc1 : c < 1) (h : c < oplus a b)
    (hab1 : oplus a b < 1) : 0 < radTan a b c := by
  have pa := cay_pos ha0 ha1
  have pb := cay_pos hb0 hb1
  have pc := cay_pos hc0 hc1
  apply uncay_pos
  rw [Real.lt_sqrt zero_le_one, one_pow, one_lt_div pc, cay_mul_cay ha0 ha1 hb0 hb1]
  exact cay_lt_cay hab1 h


def bracketCof (t X Y r m : ℝ) : ℝ :=
  (1 - t * m) / (r + X) +
    (1 - t ^ 2) * (1 - 2 * t * X + t ^ 2) /
      (((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) * (m * (1 - t * X) + t - X))

theorem bracket_identity_real {t X Y r m : ℝ} (hr : r ^ 2 = X ^ 2 + Y ^ 2)
    (hm : m ^ 2 * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) = (X - t) ^ 2 + Y ^ 2)
    (hN : 0 < (1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) (h1 : 0 < r + X)
    (h2 : 0 < m * (1 - t * X) + t - X) :
    r + m - t * (1 + r * m) = Y ^ 2 * bracketCof t X Y r m := by
  have e1 : r - X = Y ^ 2 / (r + X) := by
    rw [eq_div_iff h1.ne']
    nlinarith
  have e2 : m * (1 - t * X) - (t - X) = Y ^ 2 * ((1 - t ^ 2) * (1 - 2 * t * X + t ^ 2)) /
      (((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) * (m * (1 - t * X) + t - X)) := by
    rw [eq_div_iff (mul_pos hN h2).ne']
    linear_combination (1 - t * X) ^ 2 * hm
  have e : r + m - t * (1 + r * m) = (1 - t * m) * (r - X) + (m * (1 - t * X) - (t - X)) := by
    ring
  rw [e, e1, e2, bracketCof]
  ring

theorem bracketCof_pos {t X Y r m : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hX : X < 1)
    (hm1 : m < 1) (hN : 0 < (1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) (h1 : 0 < r + X)
    (h2 : 0 < m * (1 - t * X) + t - X) : 0 < bracketCof t X Y r m := by
  unfold bracketCof
  have a1 : 0 < 1 - t * m := by nlinarith
  have a2 : 0 < 1 - t ^ 2 := by nlinarith
  have a3 : 0 < 1 - 2 * t * X + t ^ 2 := by nlinarith
  positivity

theorem bracket_sq_aux {t X Y m : ℝ}
    (hm : m ^ 2 * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) = (X - t) ^ 2 + Y ^ 2) :
    ((m * (1 - t * X)) ^ 2 - (t - X) ^ 2) * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) =
      Y ^ 2 * ((1 - t ^ 2) * (1 - 2 * t * X + t ^ 2)) := by
  linear_combination (1 - t * X) ^ 2 * hm

theorem sq_le_bracket_aux {t X Y m : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hX : X < 1)
    (hm : m ^ 2 * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) = (X - t) ^ 2 + Y ^ 2) :
    (t - X) ^ 2 ≤ (m * (1 - t * X)) ^ 2 := by
  have hD : 0 < 1 - t * X := by nlinarith
  have hN : 0 < (1 - t * X) ^ 2 + t ^ 2 * Y ^ 2 := by positivity
  have a2 : 0 < 1 - t ^ 2 := by nlinarith
  have a3 : 0 < 1 - 2 * t * X + t ^ 2 := by nlinarith
  have key := bracket_sq_aux hm
  by_contra hc
  push Not at hc
  have h1 : ((m * (1 - t * X)) ^ 2 - (t - X) ^ 2) * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hN
  have : 0 ≤ Y ^ 2 * ((1 - t ^ 2) * (1 - 2 * t * X + t ^ 2)) := by positivity
  linarith

theorem sq_lt_bracket_aux {t X Y m : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hX : X < 1) (hY : Y ≠ 0)
    (hm : m ^ 2 * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) = (X - t) ^ 2 + Y ^ 2) :
    (t - X) ^ 2 < (m * (1 - t * X)) ^ 2 := by
  have hD : 0 < 1 - t * X := by nlinarith
  have hN : 0 < (1 - t * X) ^ 2 + t ^ 2 * Y ^ 2 := by positivity
  have a2 : 0 < 1 - t ^ 2 := by nlinarith
  have a3 : 0 < 1 - 2 * t * X + t ^ 2 := by nlinarith
  have key := bracket_sq_aux hm
  have hY2 : 0 < Y ^ 2 := by positivity
  have : 0 < Y ^ 2 * ((1 - t ^ 2) * (1 - 2 * t * X + t ^ 2)) := by positivity
  by_contra hc
  push Not at hc
  have h1 : ((m * (1 - t * X)) ^ 2 - (t - X) ^ 2) * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
  linarith

theorem bracket_den_nonneg {t X Y m : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hX : X < 1)
    (hm0 : 0 ≤ m) (hm : m ^ 2 * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) = (X - t) ^ 2 + Y ^ 2) :
    0 ≤ m * (1 - t * X) + t - X ∧ 0 ≤ m * (1 - t * X) - (t - X) := by
  have hD : 0 < 1 - t * X := by nlinarith
  have h := abs_le_of_sq_le_sq' (sq_le_bracket_aux ht0 ht1 hX hm) (by positivity)
  constructor <;> linarith [h.1, h.2]

theorem bracket_den_pos_of_im {t X Y m : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hX : X < 1)
    (hY : Y ≠ 0) (hm0 : 0 ≤ m)
    (hm : m ^ 2 * ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) = (X - t) ^ 2 + Y ^ 2) :
    0 < m * (1 - t * X) + t - X := by
  have hD : 0 < 1 - t * X := by nlinarith
  have h := abs_lt_of_sq_lt_sq' (sq_lt_bracket_aux ht0 ht1 hX hY hm) (by positivity)
  linarith [h.1]

theorem bracket_den_pos_of_re {t X m : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hX : X < 1)
    (hXt : X < t) (hm0 : 0 ≤ m) : 0 < m * (1 - t * X) + t - X := by
  have hD : 0 < 1 - t * X := by nlinarith
  have := mul_nonneg hm0 hD.le
  linarith

theorem norm_add_re_pos {W : ℂ} (h : W.im ≠ 0 ∨ 0 < W.re) : 0 < ‖W‖ + W.re := by
  have h1 : |W.re| ≤ ‖W‖ := Complex.abs_re_le_norm W
  rcases h with h | h
  · have h2 : |W.re| < ‖W‖ := by
      rw [← sq_lt_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, Complex.sq_norm,
        Complex.normSq_apply]
      have : 0 < W.im * W.im := mul_self_pos.2 h
      nlinarith
    linarith [neg_abs_le W.re]
  · linarith [le_abs_self W.re]


theorem oplus_lt_one {a b : ℝ} (ha1 : a < 1) (hb1 : b < 1) (hab : 0 < 1 + a * b) :
    oplus a b < 1 := by
  rw [oplus, div_lt_one hab]
  nlinarith

theorem oplus_comm (a b : ℝ) : oplus a b = oplus b a := by
  rw [oplus, oplus, add_comm, mul_comm]

theorem canon_add_aux {a b x y t : ℝ} (ht : oplus x y = t) (hxy : 0 < 1 + x * y)
    (ha : 1 - a * x ≠ 0) (hb : 1 - b * y ≠ 0) :
    (a - x) / (1 - a * x) + (b - y) / (1 - b * y) =
      (1 + x * y) / ((1 - a * x) * (1 - b * y)) * (a + b - t * (1 + a * b)) := by
  rw [← ht, oplus]
  field_simp
  ring

theorem normSq_one_sub_ofReal_mul (t : ℝ) (W : ℂ) :
    normSq (1 - (t : ℂ) * W) = (1 - t * W.re) ^ 2 + t ^ 2 * W.im ^ 2 := by
  rw [normSq_apply]
  simp only [sub_re, sub_im, one_re, one_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul,
    sub_zero, zero_sub]
  ring

theorem norm_mob_ofReal_sq {t : ℝ} {W : ℂ} (h : 1 - (t : ℂ) * W ≠ 0) :
    ‖mob (t : ℂ) W‖ ^ 2 * ((1 - t * W.re) ^ 2 + t ^ 2 * W.im ^ 2) =
      (W.re - t) ^ 2 + W.im ^ 2 := by
  have hN : normSq (1 - (t : ℂ) * W) ≠ 0 := normSq_eq_zero.not.2 h
  rw [Complex.sq_norm, normSq_mob_eq, Complex.conj_ofReal, ← normSq_one_sub_ofReal_mul,
    div_mul_cancel₀ _ hN, normSq_apply]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
  ring

def pairCof (t a b : ℝ) (W : ℂ) : ℝ :=
  (1 + a * b) / ((1 - ‖W‖ * a) * (1 - ‖mob (t : ℂ) W‖ * b)) *
    bracketCof t W.re W.im ‖W‖ ‖mob (t : ℂ) W‖

def pairDom (t : ℝ) : Set ℂ :=
  {W | ‖W‖ < 1 ∧ 0 < ‖W‖ + W.re ∧ 0 < ‖mob (t : ℂ) W‖ * (1 - t * W.re) + t - W.re}

theorem norm_mob_ofReal_lt_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {W : ℂ} (hW : ‖W‖ < 1) :
    ‖mob (t : ℂ) W‖ < 1 := by
  apply norm_mob_lt_one _ hW
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  exact ht1

theorem one_sub_ofReal_mul_ne_zero {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {W : ℂ}
    (hW : ‖W‖ < 1) : 1 - (t : ℂ) * W ≠ 0 := by
  have := one_sub_conj_mul_ne_zero (a := (t : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1) hW
  rwa [Complex.conj_ofReal] at this

theorem pair_bracket {t a b : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) (hab : oplus a b = t) {W : ℂ} (hW : W ∈ pairDom t) :
    (‖W‖ - a) / (1 - ‖W‖ * a) + (‖mob (t : ℂ) W‖ - b) / (1 - ‖mob (t : ℂ) W‖ * b) =
      W.im ^ 2 * pairCof t a b W := by
  obtain ⟨hW1, h1, h2⟩ := hW
  have hm1 := norm_mob_ofReal_lt_one ht0 ht1 hW1
  have hne := one_sub_ofReal_mul_ne_zero ht0 ht1 hW1
  have hX : W.re < 1 := lt_of_le_of_lt (Complex.re_le_norm W) hW1
  have hD : 0 < 1 - t * W.re := by nlinarith
  have hN : 0 < (1 - t * W.re) ^ 2 + t ^ 2 * W.im ^ 2 := by positivity
  have hm := norm_mob_ofReal_sq hne
  have hr : ‖W‖ ^ 2 = W.re ^ 2 + W.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    ring
  have e1 : 1 - ‖W‖ * a ≠ 0 := by nlinarith [norm_nonneg W]
  have e2 : 1 - ‖mob (t : ℂ) W‖ * b ≠ 0 := by nlinarith [norm_nonneg (mob (t : ℂ) W)]
  rw [canon_add_aux hab (by nlinarith) e1 e2, pairCof,
    bracket_identity_real hr (by linear_combination hm) hN h1 h2]
  ring

theorem pairCof_pos {t a b : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) {W : ℂ} (hW : W ∈ pairDom t) : 0 < pairCof t a b W := by
  obtain ⟨hW1, h1, h2⟩ := hW
  have hm1 := norm_mob_ofReal_lt_one ht0 ht1 hW1
  have hX : W.re < 1 := lt_of_le_of_lt (Complex.re_le_norm W) hW1
  have hD : 0 < 1 - t * W.re := by nlinarith
  have hN : 0 < (1 - t * W.re) ^ 2 + t ^ 2 * W.im ^ 2 := by positivity
  have e1 : 0 < 1 - ‖W‖ * a := by nlinarith [norm_nonneg W]
  have e2 : 0 < 1 - ‖mob (t : ℂ) W‖ * b := by nlinarith [norm_nonneg (mob (t : ℂ) W)]
  unfold pairCof
  have := bracketCof_pos ht0 ht1 hX hm1 hN h1 h2
  have : 0 < 1 + a * b := by positivity
  positivity

theorem mem_pairDom {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {W : ℂ} (hW : ‖W‖ < 1)
    (h1 : W.im ≠ 0 ∨ 0 < W.re) (h2 : W.im ≠ 0 ∨ W.re < t) : W ∈ pairDom t := by
  refine ⟨hW, norm_add_re_pos h1, ?_⟩
  have hX : W.re < 1 := lt_of_le_of_lt (Complex.re_le_norm W) hW
  have hm0 := norm_nonneg (mob (t : ℂ) W)
  rcases h2 with h2 | h2
  · exact bracket_den_pos_of_im ht0 ht1 hX h2 hm0
      (by linear_combination norm_mob_ofReal_sq (one_sub_ofReal_mul_ne_zero ht0 ht1 hW))
  · exact bracket_den_pos_of_re ht0 ht1 hX h2 hm0


variable (σ : CompactShape)

def tauOne : ℝ := radTan (sideOneTwo σ) (sideOneThree σ) (sideTwoThree σ)

def tauTwo : ℝ := radTan (sideOneTwo σ) (sideTwoThree σ) (sideOneThree σ)

def tauThree : ℝ := radTan (sideOneThree σ) (sideTwoThree σ) (sideOneTwo σ)

def tau : Fin 3 → ℝ
  | 0 => tauOne σ
  | 1 => tauTwo σ
  | 2 => tauThree σ

def hd : Fin 3 → ℂ → ℝ
  | 0 => fun z => ‖mob σ.vertexOne z‖
  | 1 => fun z => ‖mob σ.vertexTwo z‖
  | 2 => fun z => ‖z‖

def canon (j : Fin 3) (z : ℂ) : ℝ := (hd σ j z - tau σ j) / (1 - hd σ j z * tau σ j)

def cofZeroThree (z : ℂ) : ℝ := pairCof (sideTwoThree σ) (tauThree σ) (tauTwo σ) z

def cofOneThree (z : ℂ) : ℝ :=
  pairCof (sideOneThree σ) (tauThree σ) (tauOne σ) (exp (-((σ.θ₃ : ℂ) * I)) * z)

def cofOneTwo (z : ℂ) : ℝ :=
  pairCof (sideOneTwo σ) (tauTwo σ) (tauOne σ) (σ.rotTwo z) /
    normSq (1 - σ.vertexTwo * z) ^ 2

def domZeroThree : Set ℂ := pairDom (sideTwoThree σ)

def domOneThree : Set ℂ := {z | exp (-((σ.θ₃ : ℂ) * I)) * z ∈ pairDom (sideOneThree σ)}

def domOneTwo : Set ℂ := {z | ‖z‖ < 1 ∧ σ.rotTwo z ∈ pairDom (sideOneTwo σ)}

variable {σ}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem tauOne_pos : 0 < tauOne σ := by
  have a : 0 < sideOneTwo σ ∧ sideOneTwo σ < 1 := ⟨sideOneTwo_pos h, sideOneTwo_lt_one h⟩
  have b : 0 < sideOneThree σ ∧ sideOneThree σ < 1 :=
    ⟨sideOneThree_pos h, sideOneThree_lt_one h⟩
  have c : 0 < sideTwoThree σ ∧ sideTwoThree σ < 1 :=
    ⟨sideTwoThree_pos h, sideTwoThree_lt_one h⟩
  exact radTan_pos (by linarith) a.2 (by linarith) b.2 (by linarith) c.2 (oplus_one h)
    (oplus_lt_one a.2 b.2 (by nlinarith))

theorem tauTwo_pos : 0 < tauTwo σ := by
  have a : 0 < sideOneTwo σ ∧ sideOneTwo σ < 1 := ⟨sideOneTwo_pos h, sideOneTwo_lt_one h⟩
  have b : 0 < sideOneThree σ ∧ sideOneThree σ < 1 :=
    ⟨sideOneThree_pos h, sideOneThree_lt_one h⟩
  have c : 0 < sideTwoThree σ ∧ sideTwoThree σ < 1 :=
    ⟨sideTwoThree_pos h, sideTwoThree_lt_one h⟩
  exact radTan_pos (by linarith) a.2 (by linarith) c.2 (by linarith) b.2 (oplus_two h)
    (oplus_lt_one a.2 c.2 (by nlinarith))

theorem tauThree_pos : 0 < tauThree σ := by
  have a : 0 < sideOneTwo σ ∧ sideOneTwo σ < 1 := ⟨sideOneTwo_pos h, sideOneTwo_lt_one h⟩
  have b : 0 < sideOneThree σ ∧ sideOneThree σ < 1 :=
    ⟨sideOneThree_pos h, sideOneThree_lt_one h⟩
  have c : 0 < sideTwoThree σ ∧ sideTwoThree σ < 1 :=
    ⟨sideTwoThree_pos h, sideTwoThree_lt_one h⟩
  exact radTan_pos (by linarith) b.2 (by linarith) c.2 (by linarith) a.2 (oplus_three h)
    (oplus_lt_one b.2 c.2 (by nlinarith))

omit h in
theorem tauOne_lt_one : tauOne σ < 1 := radTan_lt_one _ _ _

omit h in
theorem tauTwo_lt_one : tauTwo σ < 1 := radTan_lt_one _ _ _

omit h in
theorem tauThree_lt_one : tauThree σ < 1 := radTan_lt_one _ _ _

theorem oplus_tauOne_tauThree : oplus (tauOne σ) (tauThree σ) = sideOneThree σ := by
  have a : 0 < sideOneTwo σ ∧ sideOneTwo σ < 1 := ⟨sideOneTwo_pos h, sideOneTwo_lt_one h⟩
  have b : 0 < sideOneThree σ ∧ sideOneThree σ < 1 :=
    ⟨sideOneThree_pos h, sideOneThree_lt_one h⟩
  have c : 0 < sideTwoThree σ ∧ sideTwoThree σ < 1 :=
    ⟨sideTwoThree_pos h, sideTwoThree_lt_one h⟩
  rw [tauOne, radTan_comm, tauThree]
  exact oplus_radTan (by linarith) b.2 (by linarith) a.2 (by linarith) c.2

theorem oplus_tauTwo_tauThree : oplus (tauTwo σ) (tauThree σ) = sideTwoThree σ := by
  have a : 0 < sideOneTwo σ ∧ sideOneTwo σ < 1 := ⟨sideOneTwo_pos h, sideOneTwo_lt_one h⟩
  have b : 0 < sideOneThree σ ∧ sideOneThree σ < 1 :=
    ⟨sideOneThree_pos h, sideOneThree_lt_one h⟩
  have c : 0 < sideTwoThree σ ∧ sideTwoThree σ < 1 :=
    ⟨sideTwoThree_pos h, sideTwoThree_lt_one h⟩
  rw [tauTwo, radTan_comm, tauThree, radTan_comm (sideOneThree σ)]
  exact oplus_radTan (by linarith) c.2 (by linarith) a.2 (by linarith) b.2

theorem oplus_tauOne_tauTwo : oplus (tauOne σ) (tauTwo σ) = sideOneTwo σ := by
  have a : 0 < sideOneTwo σ ∧ sideOneTwo σ < 1 := ⟨sideOneTwo_pos h, sideOneTwo_lt_one h⟩
  have b : 0 < sideOneThree σ ∧ sideOneThree σ < 1 :=
    ⟨sideOneThree_pos h, sideOneThree_lt_one h⟩
  have c : 0 < sideTwoThree σ ∧ sideTwoThree σ < 1 :=
    ⟨sideTwoThree_pos h, sideTwoThree_lt_one h⟩
  exact oplus_radTan (by linarith) a.2 (by linarith) b.2 (by linarith) c.2

theorem tau_mem (j : Fin 3) : 0 < tau σ j ∧ tau σ j < 1 := by
  fin_cases j
  · exact ⟨tauOne_pos h, tauOne_lt_one⟩
  · exact ⟨tauTwo_pos h, tauTwo_lt_one⟩
  · exact ⟨tauThree_pos h, tauThree_lt_one⟩

theorem hd_lt_one (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) : hd σ j z < 1 := by
  fin_cases j
  · exact norm_mob_lt_one (norm_vertexOne_lt_one h) hz
  · exact norm_mob_lt_one (norm_vertexTwo_lt_one h) hz
  · exact hz

omit h in
theorem hd_nonneg (j : Fin 3) (z : ℂ) : 0 ≤ hd σ j z := by
  fin_cases j <;> exact norm_nonneg _

theorem abs_canon_lt_one (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) : |canon σ j z| < 1 := by
  have h1 := hd_lt_one h j hz
  have h0 := hd_nonneg (σ := σ) j z
  obtain ⟨t0, t1⟩ := tau_mem h j
  have hD : 0 < 1 - hd σ j z * tau σ j := by nlinarith
  rw [canon, abs_lt, lt_div_iff₀ hD, div_lt_one hD]
  constructor <;> nlinarith


omit h in
theorem mob_ofReal_ofReal (t x : ℝ) :
    mob (t : ℂ) (x : ℂ) = (((x - t) / (1 - t * x) : ℝ) : ℂ) := by
  rw [mob, Complex.conj_ofReal]
  push_cast
  rfl

omit h in
theorem norm_mob_vertexOne_eq (z : ℂ) :
    ‖mob σ.vertexOne z‖ = ‖mob (sideOneThree σ : ℂ) (exp (-((σ.θ₃ : ℂ) * I)) * z)‖ := by
  have hu : ‖exp ((σ.θ₃ : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have ez : z = exp ((σ.θ₃ : ℂ) * I) * (exp (-((σ.θ₃ : ℂ) * I)) * z) := by
    rw [← mul_assoc, exp_mul_exp_neg, one_mul]
  conv_lhs => rw [vertexOne_eq, mul_comm, ez, mob_mul_mul hu, norm_mul, hu, one_mul]

theorem canon_add_canon_zero_three {z : ℂ} (hz : z ∈ domZeroThree σ) :
    canon σ 1 z + canon σ 2 z = σ.wallSide 0 z ^ 2 * cofZeroThree σ z := by
  have e := pair_bracket (sideTwoThree_pos h) (sideTwoThree_lt_one h) (tauThree_pos h)
    tauThree_lt_one (tauTwo_pos h) tauTwo_lt_one
    (by rw [oplus_comm]; exact oplus_tauTwo_tauThree h) hz
  rw [add_comm]
  exact e

theorem canon_add_canon_one_three {z : ℂ} (hz : z ∈ domOneThree σ) :
    canon σ 0 z + canon σ 2 z = σ.wallSide 1 z ^ 2 * cofOneThree σ z := by
  have e := pair_bracket (sideOneThree_pos h) (sideOneThree_lt_one h) (tauThree_pos h)
    tauThree_lt_one (tauOne_pos h) tauOne_lt_one
    (by rw [oplus_comm]; exact oplus_tauOne_tauThree h) hz
  have hn : ‖exp (-((σ.θ₃ : ℂ) * I)) * z‖ = ‖z‖ := by
    rw [norm_mul, show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hn, ← norm_mob_vertexOne_eq] at e
  rw [add_comm, wallSide_one_eq_neg_im, neg_sq]
  exact e

theorem canon_add_canon_one_two {z : ℂ} (hz : z ∈ domOneTwo σ) :
    canon σ 0 z + canon σ 1 z = σ.wallSide 2 z ^ 2 * cofOneTwo σ z := by
  have e := pair_bracket (sideOneTwo_pos h) (sideOneTwo_lt_one h) (tauTwo_pos h)
    tauTwo_lt_one (tauOne_pos h) tauOne_lt_one
    (by rw [oplus_comm]; exact oplus_tauOne_tauTwo h) hz.2
  have h1 := norm_disc_vertexOne_eq h hz.1
  rw [CompactShape.disc_eq_mob h] at h1
  rw [norm_rotTwo h, ← h1] at e
  have hN := normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h hz.1)
  rw [add_comm, wallSide_two_eq_rotTwo h, cofOneTwo]
  change (‖mob σ.vertexTwo z‖ - tauTwo σ) / (1 - ‖mob σ.vertexTwo z‖ * tauTwo σ) +
    (‖mob σ.vertexOne z‖ - tauOne σ) / (1 - ‖mob σ.vertexOne z‖ * tauOne σ) = _
  rw [e]
  field_simp

theorem cofZeroThree_pos {z : ℂ} (hz : z ∈ domZeroThree σ) : 0 < cofZeroThree σ z :=
  pairCof_pos (sideTwoThree_pos h) (sideTwoThree_lt_one h) (tauThree_pos h) tauThree_lt_one
    (tauTwo_pos h) tauTwo_lt_one hz

theorem cofOneThree_pos {z : ℂ} (hz : z ∈ domOneThree σ) : 0 < cofOneThree σ z :=
  pairCof_pos (sideOneThree_pos h) (sideOneThree_lt_one h) (tauThree_pos h) tauThree_lt_one
    (tauOne_pos h) tauOne_lt_one hz

theorem cofOneTwo_pos {z : ℂ} (hz : z ∈ domOneTwo σ) : 0 < cofOneTwo σ z := by
  have hN := normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h hz.1)
  have := pairCof_pos (sideOneTwo_pos h) (sideOneTwo_lt_one h) (tauTwo_pos h) tauTwo_lt_one
    (tauOne_pos h) tauOne_lt_one hz.2
  unfold cofOneTwo
  positivity


omit h in
theorem re_nonneg_of_mem {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ z.re :=
  re_nonneg_of_sector (θ₃_pos σ) (θ₃_le σ) (sector_three hz).1 (sector_three hz).2

omit h in
theorem eq_ofReal_of_im {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [hz])

theorem mem_domZeroThree {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h2 : z ≠ σ.vertexTwo) :
    z ∈ domZeroThree σ := by
  have hz1 := norm_lt_one_of_mem h hz
  have hre := re_nonneg_of_mem hz
  have t0 := sideTwoThree_pos h
  have t1 := sideTwoThree_lt_one h
  apply mem_pairDom t0 t1 hz1
  · by_cases hi : z.im = 0
    · right
      rcases hre.lt_or_eq with hr | hr
      · exact hr
      · exact absurd (Complex.ext (by simp [← hr]) (by simp [hi])) h0
    · exact Or.inl hi
  · by_cases hi : z.im = 0
    · right
      by_contra hc
      push Not at hc
      have hx : z = (z.re : ℂ) := eq_ofReal_of_im hi
      rcases hc.lt_or_eq with hc | hc
      · have hw := hz.2 2
        rw [hx, wallSide_two_ofReal h] at hw
        have hr1 : z.re < 1 := lt_of_le_of_lt (Complex.re_le_norm z) hz1
        have : 0 < 1 - sideTwoThree σ * z.re := by nlinarith
        have := mul_pos (mul_pos (sin_pos_of_le (θ₂_pos σ) (θ₂_le σ))
          (show 0 < z.re - sideTwoThree σ by linarith)) this
        nlinarith
      · exact h2 (by rw [hx, vertexTwo_eq, hc])
    · exact Or.inl hi

theorem mem_domOneThree {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) :
    z ∈ domOneThree σ := by
  have hz1 := norm_lt_one_of_mem h hz
  set W := exp (-((σ.θ₃ : ℂ) * I)) * z with hW
  have hn : ‖W‖ = ‖z‖ := by
    rw [hW, norm_mul, show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  have ez : z = exp ((σ.θ₃ : ℂ) * I) * W := by
    rw [hW, ← mul_assoc, exp_mul_exp_neg, one_mul]
  have hWi : W.im = -σ.wallSide 1 z := by
    rw [wallSide_one_eq_neg_im, neg_neg]
  have hre : 0 ≤ W.re := by
    have e1 : (conj W).im = σ.wallSide 1 z := by rw [Complex.conj_im, hWi, neg_neg]
    have e2 : (exp (-((σ.θ₃ : ℂ) * I)) * conj W).im = -z.im := by
      have : exp (-((σ.θ₃ : ℂ) * I)) * conj W = conj z := by
        rw [hW, map_mul, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal,
          Complex.conj_I, ← mul_assoc, ← Complex.exp_add]
        ring_nf
        rw [Complex.exp_zero, one_mul]
      rw [this, Complex.conj_im]
    have := re_nonneg_of_sector (θ₃_pos σ) (θ₃_le σ) (W := conj W) (by rw [e1]; exact hz.2 1)
      (by rw [e2]; have h00 : 0 ≤ z.im := hz.2 0; linarith)
    rwa [Complex.conj_re] at this
  have t0 := sideOneThree_pos h
  have t1 := sideOneThree_lt_one h
  change W ∈ pairDom (sideOneThree σ)
  apply mem_pairDom t0 t1 (by rw [hn]; exact hz1)
  · by_cases hi : W.im = 0
    · right
      rcases hre.lt_or_eq with hr | hr
      · exact hr
      · have : W = 0 := Complex.ext (by simp [← hr]) (by simp [hi])
        exact absurd (by rw [ez, this, mul_zero]) h0
    · exact Or.inl hi
  · by_cases hi : W.im = 0
    · right
      by_contra hc
      push Not at hc
      have hx : W = (W.re : ℂ) := eq_ofReal_of_im hi
      rcases hc.lt_or_eq with hc | hc
      · have hw := hz.2 2
        have hr := wallSide_two_ray h W.re
        rw [← mul_comm (exp _), ← hx, ← ez] at hr
        have hr1 : W.re < 1 := lt_of_le_of_lt (Complex.re_le_norm W) (by rw [hn]; exact hz1)
        have a1 : 0 < 1 - sideOneThree σ * W.re := by nlinarith
        have a2 := mul_pos (mul_pos (mul_pos (sideTwoThree_pos h)
          (sin_pos_of_le (θ₂_pos σ) (θ₂_le σ))) (show 0 < W.re - sideOneThree σ by linarith)) a1
        nlinarith
      · exact h1 (by rw [ez, hx, vertexOne_eq, hc, mul_comm])
    · exact Or.inl hi


theorem rotTwo_injOn {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (e : σ.rotTwo z = σ.rotTwo w) :
    z = w := by
  rw [rotTwo_eq_mul_mob h, rotTwo_eq_mul_mob h] at e
  have e' := mul_left_cancel₀ (neg_ne_zero.2 (Complex.exp_ne_zero _)) e
  rw [← mobInv_mob (normSq_vertexTwo_ne_one h)
      (one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz), e',
    mobInv_mob (normSq_vertexTwo_ne_one h)
      (one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hw)]

theorem rotTwo_vertexTwo : σ.rotTwo σ.vertexTwo = 0 := by
  rw [rotTwo_eq_mul_mob h, mob_self, mul_zero]

theorem mem_domOneTwo {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) : z ∈ domOneTwo σ := by
  have hz1 := norm_lt_one_of_mem h hz
  set W := σ.rotTwo z with hW
  have hW1 : ‖W‖ < 1 := norm_rotTwo_lt_one h hz1
  have hs := sector_two h hz
  have hre : 0 ≤ W.re := re_nonneg_of_sector (θ₂_pos σ) (θ₂_le σ) hs.1 hs.2
  have t0 := sideOneTwo_pos h
  have t1 := sideOneTwo_lt_one h
  refine ⟨hz1, mem_pairDom t0 t1 hW1 ?_ ?_⟩
  · by_cases hi : W.im = 0
    · right
      rcases hre.lt_or_eq with hr | hr
      · exact hr
      · have : W = 0 := Complex.ext (by simp [← hr]) (by simp [hi])
        refine absurd (rotTwo_injOn h hz1 (norm_vertexTwo_lt_one h) ?_) h2
        rw [← hW, this, rotTwo_vertexTwo h]
    · exact Or.inl hi
  · by_cases hi : W.im = 0
    · right
      by_contra hc
      push Not at hc
      have hx : W = (W.re : ℂ) := eq_ofReal_of_im hi
      rcases hc.lt_or_eq with hc | hc
      · have hr1 : W.re < 1 := lt_of_le_of_lt (Complex.re_le_norm W) hW1
        have hone := (sector_one h hz).1
        rw [rotOne_eq_mob_rotTwo h hz1, ← hW, hx, mob_ofReal_ofReal,
          exp_ofReal_mul_I_eq] at hone
        simp only [neg_mul, neg_im, mul_im, add_re, add_im, ofReal_re, ofReal_im, mul_re,
          I_re, I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add] at hone
        have a1 : 0 < 1 - sideOneTwo σ * W.re := by nlinarith
        have a2 : 0 < (W.re - sideOneTwo σ) / (1 - sideOneTwo σ * W.re) :=
          div_pos (by linarith) a1
        have a3 := sin_pos_of_le (θ₁_pos σ) (θ₁_le σ)
        nlinarith
      · refine absurd (rotTwo_injOn h hz1 (norm_vertexOne_lt_one h) ?_) h1
        rw [← hW, hx, rotTwo_vertexOne h, hW, ← hc]
    · exact Or.inl hi

end Hyp

end HypFold

end GC.Seifert
