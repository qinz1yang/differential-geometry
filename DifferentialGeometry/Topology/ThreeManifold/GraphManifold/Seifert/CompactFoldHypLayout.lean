import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypPreFold

/-!
# The layout of the hyperbolic compact fold: a small core above the contact point

Lane CF-H3, tier 3 (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, curvature `-1`, with review 23 §6:
shape-dependent parameters). The contact chart `pChart z = mob τ₂ (rotTwo z)` is a disc
automorphism sending the incircle contact point `P₁₂` of wall 2 to `0`, `v₂` to `-τ₂`, `v₁` to `τ₁`
and wall 2 to the real diameter (`rotTwo_eq_mob_pChart`, `hd_zero_eq_pChart`,
`hd_one_eq_pChart`); the lens coordinate is `2 Im Z/(1 - |Z|²)` in it (`lensCoord_eq_pChart`).

The corner regions `canon j < -e` are hyperbolic discs; in the chart their complements are
`(X ∓ e)(cX ∓ N) + cY² ≥ 0` with explicit `c, N` (`hyp_gap_bound`), so a point of the triangle
outside both corner regions at height `Y` has `|X| ≤ e + 4Y²/(τⱼ(1 - τⱼ²))`: the sector condition
at the vertex excludes the far side of the corner disc. All parameters are proportional to
`layoutScale = min (τₘ cₘ sₘ, τ₃)` with `τₘ = min τⱼ`, `cₘ = min (1 - τⱼ²)`, `sₘ = min sin θⱼ`
(`hypLayout`): lens `β = μ/64`, switch top `β' = μ/32`, corner shrink `e = μ/1024`, inner germ
and blend `τₘ/4 < τₘ/3 < τₘ/2`, outer germ and blend `b₃/4 < b₃/2 < b₃ = min (τ₃/2, 1/5)`.

The core is the hyperbolic disc `‖mob (hypCoreCenter σ) z‖ < hypCoreRadius σ = 6u` with margin
`hypCoreMargin σ = u`, `u = coreUnit σ = μ/1024`, centred at `pChartInv (12u·i)`, i.e. the
pseudo-hyperbolic disc about `12u·i` in the chart (`norm_mob_hypCoreCenter`). The switch window
`{canon j ≥ -e, β ≤ lensCoord ≤ β'} ∩ T` lies in the shrunk core (`window_mem_core`), and every
point of `T` outside both corner regions below the switch top is within `|X| ≤ 2u`, `Y ≤ 16u`
(`pChart_small`). The core with its margin lies in the open triangle
(`mem_openTriangle_of_core`), and the core is far from the germ discs and the wall strips
(`core_separation`). The parameter facts consumed by the wall stage are `hypLayout_params`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

theorem hyp_gap_bound {τ e X Y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (he0 : 0 < e) (he : 2 * e ≤ τ)
    (hY0 : 0 ≤ Y) (hY : 64 * Y ≤ τ * (1 - τ ^ 2)) (hX1 : X < 1)
    (hout : (τ - e) ^ 2 * ((1 - τ * X) ^ 2 + τ ^ 2 * Y ^ 2) ≤
      (1 - τ * e) ^ 2 * ((X - τ) ^ 2 + Y ^ 2))
    (hsec : (X - τ) * (1 - τ * X) ≤ τ * Y ^ 2) :
    X ≤ e + 4 * Y ^ 2 / (τ * (1 - τ ^ 2)) := by
  have hq : 0 < 1 - τ ^ 2 := by nlinarith
  have hτ' : 0 < 1 - τ := by linarith
  have hP : 0 < τ * (1 - τ ^ 2) := mul_pos hτ0 hq
  set c := 1 + τ ^ 2 - 2 * τ * e with hc
  set N := 2 * τ - τ ^ 2 * e - e with hN
  have hc1 : 1 ≤ c := by nlinarith
  have hc2 : c ≤ 2 := by nlinarith
  have hid : (1 - τ * e) ^ 2 * ((X - τ) ^ 2 + Y ^ 2) -
      (τ - e) ^ 2 * ((1 - τ * X) ^ 2 + τ ^ 2 * Y ^ 2) =
      (1 - τ ^ 2) * ((X - e) * (c * X - N) + c * Y ^ 2) := by
    rw [hc, hN]; ring
  have key : (X - e) * (N - c * X) ≤ c * Y ^ 2 := by
    have h0 : 0 ≤ (1 - τ ^ 2) * ((X - e) * (c * X - N) + c * Y ^ 2) := by
      rw [← hid]; linarith
    have := (mul_nonneg_iff_of_pos_left hq).1 h0
    linarith
  have hNτ : N - c * τ = (1 - τ ^ 2) * (τ - e) := by rw [hc, hN]; ring
  have hY4 : 4096 * Y ^ 2 ≤ (τ * (1 - τ ^ 2)) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity : 0 ≤ 64 * Y) hY 2
    nlinarith
  have hcY : c * Y ^ 2 ≤ 2 * Y ^ 2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg Y)
  have hτe : τ / 2 ≤ τ - e := by linarith
  have hqe : (1 - τ ^ 2) * (τ / 2) ≤ (1 - τ ^ 2) * (τ - e) :=
    mul_le_mul_of_nonneg_left hτe hq.le
  rw [← sub_le_iff_le_add', le_div_iff₀ hP]
  by_contra hlt
  push Not at hlt
  have hXe : 0 < X - e := by
    by_contra hn
    push Not at hn
    have : (X - e) * (τ * (1 - τ ^ 2)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn hP.le
    nlinarith [sq_nonneg Y]
  rcases le_or_gt X τ with hXτ | hXτ
  · have hcx : 0 ≤ c * (τ - X) := mul_nonneg (by linarith) (by linarith)
    have h1 : (1 - τ ^ 2) * τ / 2 ≤ N - c * X := by
      have : N - c * X = (N - c * τ) + c * (τ - X) := by ring
      rw [this, hNτ]
      linarith
    have h2 : (X - e) * ((1 - τ ^ 2) * τ / 2) ≤ (X - e) * (N - c * X) :=
      mul_le_mul_of_nonneg_left h1 hXe.le
    nlinarith
  · have hX0 : 0 ≤ X - τ := sub_nonneg.2 hXτ.le
    have h1 : (X - τ) * (1 - τ) ≤ τ * Y ^ 2 := by
      have : (X - τ) * (1 - τ) ≤ (X - τ) * (1 - τ * X) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hX0
      linarith
    have h3 : c * (X - τ) * (1 - τ) ≤ 2 * τ * Y ^ 2 := by
      have : c * (X - τ) ≤ 2 * (X - τ) := mul_le_mul_of_nonneg_right hc2 hX0
      have := mul_le_mul_of_nonneg_right this hτ'.le
      linarith
    have hq2 : (1 - τ ^ 2) ^ 2 ≤ 2 * (1 - τ ^ 2) * (1 - τ) := by
      have e : (1 - τ ^ 2) ^ 2 = (1 - τ ^ 2) * (1 - τ) * (1 + τ) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left (by linarith : 1 + τ ≤ 2) (mul_nonneg hq.le hτ'.le)
      linarith
    have hP2 : (τ * (1 - τ ^ 2)) ^ 2 ≤ (1 - τ ^ 2) ^ 2 := by
      have : τ * (1 - τ ^ 2) ≤ 1 - τ ^ 2 := mul_le_of_le_one_left hq.le hτ1.le
      exact pow_le_pow_left₀ hP.le this 2
    have h4 : 2 * τ * Y ^ 2 ≤ (1 - τ) * (τ * (1 - τ ^ 2) / 4) := by
      have hpos : 0 ≤ (1 - τ ^ 2) * (1 - τ) := mul_nonneg hq.le hτ'.le
      have h8 : 8 * Y ^ 2 ≤ (1 - τ) * (1 - τ ^ 2) := by linarith
      have := mul_le_mul_of_nonneg_left h8 (by linarith : (0 : ℝ) ≤ τ / 4)
      linarith
    have h5 : c * (X - τ) ≤ τ * (1 - τ ^ 2) / 4 := by
      have : c * (X - τ) * (1 - τ) ≤ τ * (1 - τ ^ 2) / 4 * (1 - τ) := by linarith
      exact le_of_mul_le_mul_right this hτ'
    have h6 : τ * (1 - τ ^ 2) / 4 ≤ N - c * X := by
      have : N - c * X = (N - c * τ) - c * (X - τ) := by ring
      rw [this, hNτ]
      linarith
    have h7 : τ / 2 * (τ * (1 - τ ^ 2) / 4) ≤ (X - e) * (N - c * X) :=
      mul_le_mul (by linarith) h6 (by positivity) hXe.le
    have h8 : (τ * (1 - τ ^ 2)) ^ 2 ≤ τ ^ 2 * (1 - τ ^ 2) := by
      have : 1 - τ ^ 2 ≤ 1 := by have := sq_nonneg τ; linarith
      have h' : (τ * (1 - τ ^ 2)) ^ 2 = τ ^ 2 * (1 - τ ^ 2) * (1 - τ ^ 2) := by ring
      rw [h']
      exact mul_le_of_le_one_right (by positivity) this
    have h9 : 0 < τ ^ 2 * (1 - τ ^ 2) := by positivity
    linarith

theorem mob_mob_neg_ofReal {a b : ℝ} {Z : ℂ} (hb : 1 + (b : ℂ) * Z ≠ 0)
    (hd : (1 + (b : ℂ) * Z) - a * (Z + b) ≠ 0)
    (hc : 1 - (((a - b) / (1 - a * b) : ℝ) : ℂ) * Z ≠ 0) (hab : 1 - a * b ≠ 0) :
    mob (a : ℂ) (mob (-(b : ℂ)) Z) = mob (((a - b) / (1 - a * b) : ℝ) : ℂ) Z := by
  have hm : mob (-(b : ℂ)) Z = (Z + b) / (1 + b * Z) := by
    simp only [mob, map_neg, Complex.conj_ofReal, sub_neg_eq_add, neg_mul]
  have hW : (Z + b) / (1 + b * Z) * (1 + b * Z) = Z + b := div_mul_cancel₀ _ hb
  rw [hm, mob, Complex.conj_ofReal]
  set W := (Z + b) / (1 + b * Z) with hWdef
  have h1aW : 1 - (a : ℂ) * W ≠ 0 := by
    intro h0
    apply hd
    linear_combination (1 + (b : ℂ) * Z) * h0 + (a : ℂ) * hW
  rw [div_eq_div_iff h1aW hd |>.mpr (by linear_combination (1 - (a : ℂ) ^ 2) * hW :
    (W - a) * ((1 + (b : ℂ) * Z) - a * (Z + b)) = ((Z + b) - a * (1 + b * Z)) * (1 - a * W))]
  have hab' : (1 : ℂ) - a * b ≠ 0 := by exact_mod_cast hab
  have hcdef : ((((a - b) / (1 - a * b) : ℝ) : ℂ)) * (1 - a * b) = a - b := by
    push_cast
    field_simp
  rw [mob, Complex.conj_ofReal, div_eq_div_iff hd hc]
  linear_combination (1 - Z ^ 2) * hcdef

theorem re_mob_mul_normSq (a z : ℂ) :
    (mob a z).re * normSq (1 - conj a * z) = ((z - a) * conj (1 - conj a * z)).re := by
  by_cases h : 1 - conj a * z = 0
  · simp [h]
  · rw [← mob_mul_normSq h, Complex.mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

theorem re_mob_ofReal (t : ℝ) (W : ℂ) :
    (mob (t : ℂ) W).re * normSq (1 - (t : ℂ) * W) =
      (W.re - t) * (1 - t * W.re) - t * W.im ^ 2 := by
  have e := re_mob_mul_normSq (t : ℂ) W
  rw [Complex.conj_ofReal] at e
  rw [e]
  simp only [mul_re, mul_im, sub_re, sub_im, ofReal_re, ofReal_im, conj_re, conj_im, one_re,
    one_im, map_sub, map_one, map_mul, Complex.conj_ofReal]
  ring

theorem outside_of_canonForm {τ e ϖ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (he : e ≤ τ)
    (hϖ1 : ϖ < 1) (hc : -e ≤ canonForm τ ϖ) :
    (τ - e) ^ 2 ≤ (1 - τ * e) ^ 2 * ϖ ^ 2 := by
  have hD : 0 < 1 - ϖ * τ := by nlinarith
  rw [canonForm, le_div_iff₀ hD] at hc
  have h1 : τ - e ≤ (1 - τ * e) * ϖ := by nlinarith
  have h2 : 0 ≤ τ - e := by linarith
  have := pow_le_pow_left₀ h2 h1 2
  nlinarith

theorem xbound_of_mob {τ e : ℝ} {Z : ℂ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (he0 : 0 < e)
    (he : 2 * e ≤ τ) (hZ : ‖Z‖ < 1) (hY0 : 0 ≤ Z.im) (hY : 64 * Z.im ≤ τ * (1 - τ ^ 2))
    (hc : -e ≤ canonForm τ ‖mob (τ : ℂ) Z‖) (hs : (mob (τ : ℂ) Z).re ≤ 0) :
    Z.re ≤ e + 4 * Z.im ^ 2 / (τ * (1 - τ ^ 2)) := by
  have hne := one_sub_ofReal_mul_ne_zero hτ0 hτ1 hZ
  have hN : 0 < normSq (1 - (τ : ℂ) * Z) := normSq_pos.2 hne
  have hm := norm_mob_ofReal_lt_one hτ0 hτ1 hZ
  have ho := outside_of_canonForm hτ0 hτ1 (by linarith) hm hc
  have hsq := norm_mob_ofReal_sq hne
  have hX1 : Z.re < 1 := lt_of_le_of_lt (Complex.re_le_norm Z) hZ
  apply hyp_gap_bound hτ0 hτ1 he0 he hY0 hY hX1
  · have hB : 0 ≤ (1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right ho hB
    calc (τ - e) ^ 2 * ((1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2)
        ≤ (1 - τ * e) ^ 2 * ‖mob (τ : ℂ) Z‖ ^ 2 *
          ((1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2) := this
      _ = (1 - τ * e) ^ 2 * ((Z.re - τ) ^ 2 + Z.im ^ 2) := by rw [mul_assoc, hsq]
      _ = (1 - τ * e) ^ 2 * ((Z.re - τ) ^ 2 + Z.im ^ 2) := rfl
  · have e1 := re_mob_ofReal τ Z
    have := mul_nonpos_of_nonpos_of_nonneg hs hN.le
    linarith

theorem canonForm_half_lt {τ e b : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hb0 : 0 ≤ b)
    (hb : 2 * b ≤ τ) (he0 : 0 ≤ e) (he : 4 * e ≤ τ) : canonForm τ b < -e := by
  have hD : 0 < 1 - b * τ := by nlinarith
  rw [canonForm, div_lt_iff₀ hD]
  nlinarith [mul_nonneg (mul_nonneg hb0 hτ0.le) he0]

theorem mob_ofReal_neg_conj (t : ℝ) (Z : ℂ) :
    mob (t : ℂ) (-conj Z) = -conj (mob (-(t : ℂ)) Z) := by
  simp only [mob, map_neg, Complex.conj_ofReal, map_div₀, sub_neg_eq_add, neg_mul, map_add,
    map_one, map_mul]
  rw [← neg_div]
  congr 1 <;> ring

theorem norm_mob_ofReal_neg_conj (t : ℝ) (Z : ℂ) :
    ‖mob (t : ℂ) (-conj Z)‖ = ‖mob (-(t : ℂ)) Z‖ := by
  rw [mob_ofReal_neg_conj, norm_neg, Complex.norm_conj]

theorem re_mob_ofReal_neg_conj (t : ℝ) (Z : ℂ) :
    (mob (t : ℂ) (-conj Z)).re = -(mob (-(t : ℂ)) Z).re := by
  rw [mob_ofReal_neg_conj, neg_re, Complex.conj_re]

theorem small_of_mob {τ u : ℝ} {Z : ℂ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hu : 0 < u)
    (hμ : 1024 * u ≤ τ * (1 - τ ^ 2)) (hZ : ‖Z‖ < 1) (hY0 : 0 ≤ Z.im)
    (hY : Z.im ≤ 16 * u) (hc : -u ≤ canonForm τ ‖mob (τ : ℂ) Z‖)
    (hs : (mob (τ : ℂ) Z).re ≤ 0) : Z.re ≤ 2 * u := by
  have hq : 0 < 1 - τ ^ 2 := by nlinarith
  have hP : 0 < τ * (1 - τ ^ 2) := mul_pos hτ0 hq
  have hPτ : τ * (1 - τ ^ 2) ≤ τ := mul_le_of_le_one_right hτ0.le (by nlinarith)
  have hx := xbound_of_mob hτ0 hτ1 hu (by linarith) hZ hY0 (by linarith) hc hs
  have hb : 4 * Z.im ^ 2 / (τ * (1 - τ ^ 2)) ≤ u := by
    rw [div_le_iff₀ hP]
    have : Z.im ^ 2 ≤ (16 * u) ^ 2 := pow_le_pow_left₀ hY0 hY 2
    nlinarith
  linarith

theorem pseudo_triangle {τ : ℝ} {Z : ℂ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hZ : ‖Z‖ < 1) :
    ‖mob (τ : ℂ) Z‖ * (1 + τ * ‖Z‖) ≤ τ + ‖Z‖ := by
  have hXr := Complex.abs_re_le_norm Z
  rw [abs_le] at hXr
  have hD0 : 0 < 1 - τ * Z.re := by nlinarith [norm_nonneg Z]
  have hne : 1 - (τ : ℂ) * Z ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      zero_re] at this
    linarith
  have hsq := norm_mob_ofReal_sq hne
  have hr : ‖Z‖ ^ 2 = Z.re ^ 2 + Z.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  have hD : 0 < (1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2 := by positivity
  have hid : (τ + ‖Z‖) ^ 2 * ((1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2) -
      ((Z.re - τ) ^ 2 + Z.im ^ 2) * (1 + τ * ‖Z‖) ^ 2 =
        (1 - τ ^ 2) * (1 - ‖Z‖ ^ 2) * (2 * τ * (‖Z‖ + Z.re)) := by
    have : Z.im ^ 2 = ‖Z‖ ^ 2 - Z.re ^ 2 := by linarith
    rw [this]; ring
  have hnn : 0 ≤ (1 - τ ^ 2) * (1 - ‖Z‖ ^ 2) * (2 * τ * (‖Z‖ + Z.re)) := by
    have h1 : 0 ≤ 1 - τ ^ 2 := by nlinarith
    have h2 : 0 ≤ 1 - ‖Z‖ ^ 2 := by nlinarith [norm_nonneg Z]
    have h3 : 0 ≤ 2 * τ * (‖Z‖ + Z.re) := mul_nonneg (by positivity) (by linarith)
    positivity
  have e2 : (‖mob (τ : ℂ) Z‖ * (1 + τ * ‖Z‖)) ^ 2 *
      ((1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2) =
      ((Z.re - τ) ^ 2 + Z.im ^ 2) * (1 + τ * ‖Z‖) ^ 2 := by
    rw [← hsq]; ring
  have key : (‖mob (τ : ℂ) Z‖ * (1 + τ * ‖Z‖)) ^ 2 ≤ (τ + ‖Z‖) ^ 2 := by
    have : (‖mob (τ : ℂ) Z‖ * (1 + τ * ‖Z‖)) ^ 2 * ((1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2) ≤
        (τ + ‖Z‖) ^ 2 * ((1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2) := by linarith
    exact le_of_mul_le_mul_right this hD
  have h0 : 0 ≤ τ + ‖Z‖ := by positivity
  exact le_of_pow_le_pow_left₀ two_ne_zero h0 key

theorem canonForm_le_of_triangle {τ ϖ r : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hϖ1 : ϖ < 1)
    (h : ϖ * (1 + τ * r) ≤ τ + r) : canonForm τ ϖ ≤ r := by
  have hD : 0 < 1 - ϖ * τ := by nlinarith
  rw [canonForm, div_le_iff₀ hD]
  nlinarith

theorem ge_of_canonForm {τ ϖ s : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ < 1)
    (hs : 0 ≤ s) (h : -s ≤ canonForm τ ϖ) : τ - s ≤ ϖ := by
  have hD : 0 < 1 - ϖ * τ := by nlinarith
  rw [canonForm, le_div_iff₀ hD] at h
  nlinarith [mul_nonneg hs (mul_nonneg hϖ0 hτ0)]

theorem norm_exp_neg_ofReal_mul_I (x : ℝ) : ‖exp (-((x : ℂ) * I))‖ = 1 := by
  rw [show -((x : ℂ) * I) = ((-x : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_mob_I_sq {k : ℝ} {Z : ℂ} (hk : |k| < 1) (hZ : ‖Z‖ < 1) :
    ‖mob ((k : ℂ) * I) Z‖ ^ 2 * ((1 - k * Z.im) ^ 2 + (k * Z.re) ^ 2) =
      Z.re ^ 2 + (Z.im - k) ^ 2 := by
  have hk' : ‖(k : ℂ) * I‖ < 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hk
  have hne := one_sub_conj_mul_ne_zero hk' hZ
  have hN : normSq (1 - conj ((k : ℂ) * I) * Z) ≠ 0 := normSq_eq_zero.not.2 hne
  have e1 : normSq (1 - conj ((k : ℂ) * I) * Z) = (1 - k * Z.im) ^ 2 + (k * Z.re) ^ 2 := by
    rw [normSq_apply]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, sub_re, sub_im, one_re, one_im,
      mul_re, mul_im, ofReal_re, ofReal_im, neg_re, neg_im, I_re, I_im]
    ring
  have e2 : normSq (Z - (k : ℂ) * I) = Z.re ^ 2 + (Z.im - k) ^ 2 := by
    rw [normSq_apply]
    simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  rw [Complex.sq_norm, normSq_mob_eq, ← e1, div_mul_cancel₀ _ hN, e2]

theorem im_rot_mob_neg (θ τ : ℝ) (Z : ℂ) :
    (exp (-((θ : ℂ) * I)) * mob (-(τ : ℂ)) Z).im * normSq (1 + (τ : ℂ) * Z) =
      Z.im * (1 - τ ^ 2) * Real.cos θ -
        (Z.re * (1 + τ ^ 2) + τ * (1 + Z.re ^ 2 + Z.im ^ 2)) * Real.sin θ := by
  have hrw : (1 : ℂ) + τ * Z = 1 - conj (-(τ : ℂ)) * Z := by
    rw [map_neg, Complex.conj_ofReal]; ring
  by_cases h0 : (1 : ℂ) + τ * Z = 0
  · have hZ : Z = -1 / τ := by
      have hτ : (τ : ℂ) ≠ 0 := by
        intro ht; rw [ht] at h0; simp at h0
      field_simp
      linear_combination h0
    have hre : Z.re = -1 / τ := by rw [hZ]; simp
    have him : Z.im = 0 := by rw [hZ]; simp
    have hτ : τ ≠ 0 := by
      intro ht; rw [ht] at h0; simp at h0
    rw [h0, map_zero, mul_zero, hre, him]
    field_simp
    ring
  · have e := mob_mul_normSq (a := -(τ : ℂ)) (z := Z) (by rw [← hrw]; exact h0)
    rw [← hrw] at e
    have : (exp (-((θ : ℂ) * I)) * mob (-(τ : ℂ)) Z).im * normSq (1 + (τ : ℂ) * Z) =
        (exp (-((θ : ℂ) * I)) * (mob (-(τ : ℂ)) Z * (normSq (1 + (τ : ℂ) * Z) : ℂ))).im := by
      rw [← mul_assoc, Complex.im_mul_ofReal]
    rw [this, e, exp_neg_ofReal_mul_I_eq]
    simp only [mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im, map_add,
      map_one, map_mul, Complex.conj_ofReal, conj_re, conj_im, add_re, add_im, one_re, one_im,
      sub_neg_eq_add]
    ring

theorem im_rot_mob (θ τ : ℝ) (Z : ℂ) :
    (-exp ((θ : ℂ) * I) * mob (τ : ℂ) Z).im * normSq (1 - (τ : ℂ) * Z) =
      (τ * (1 + Z.re ^ 2 + Z.im ^ 2) - Z.re * (1 + τ ^ 2)) * Real.sin θ -
        Z.im * (1 - τ ^ 2) * Real.cos θ := by
  have hrw : (1 : ℂ) - τ * Z = 1 - conj (τ : ℂ) * Z := by rw [Complex.conj_ofReal]
  by_cases h0 : (1 : ℂ) - τ * Z = 0
  · have hτ : τ ≠ 0 := by
      intro ht; rw [ht] at h0; simp at h0
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
    have hZ : Z = 1 / τ := by
      rw [eq_div_iff hτc]
      linear_combination -h0
    have hre : Z.re = 1 / τ := by rw [hZ]; simp
    have him : Z.im = 0 := by rw [hZ]; simp
    rw [h0, map_zero, mul_zero, hre, him]
    field_simp
    ring
  · have e := mob_mul_normSq (a := (τ : ℂ)) (z := Z) (by rw [← hrw]; exact h0)
    rw [← hrw] at e
    have : (-exp ((θ : ℂ) * I) * mob (τ : ℂ) Z).im * normSq (1 - (τ : ℂ) * Z) =
        (-exp ((θ : ℂ) * I) * (mob (τ : ℂ) Z * (normSq (1 - (τ : ℂ) * Z) : ℂ))).im := by
      rw [← mul_assoc, Complex.im_mul_ofReal]
    rw [this, e, exp_ofReal_mul_I_eq]
    simp only [mul_im, mul_re, neg_re, neg_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im,
      map_sub, map_one, map_mul, Complex.conj_ofReal, conj_re, conj_im, add_re, add_im, one_re,
      one_im]
    ring

theorem window_aux {u X Y : ℝ} (hu : 0 < u) (hu1 : 1024 * u ≤ 1) (hX : |X| ≤ 2 * u)
    (hY0 : 0 ≤ Y) (hY : Y ≤ 16 * u) (hlo : 8 * u * (1 - (X ^ 2 + Y ^ 2)) ≤ Y) :
    X ^ 2 + (Y - 12 * u) ^ 2 < 25 * u ^ 2 * (1 - 12 * u * Y) ^ 2 := by
  have hX2 : X ^ 2 ≤ 4 * u ^ 2 := by
    have := sq_le_sq' (abs_le.1 hX).1 (abs_le.1 hX).2
    linarith
  have hY2 : Y ^ 2 ≤ 256 * u ^ 2 := by nlinarith
  have hu2 : 2080 * u ^ 2 ≤ 1 / 400 := by nlinarith
  have hlo' : 8 * u - u / 400 ≤ Y := by
    have : 8 * u * (X ^ 2 + Y ^ 2) ≤ 8 * u * (260 * u ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hc : (Y - 12 * u) ^ 2 ≤ (4 * u + u / 400) ^ 2 := by
    apply sq_le_sq'
    · linarith
    · linarith
  have h12 : 12 * u * Y ≤ 192 * u ^ 2 := by nlinarith
  have hu3 : 192 * u ^ 2 ≤ 1 / 4096 := by nlinarith
  have h1 : 1 - 1 / 4096 ≤ 1 - 12 * u * Y := by linarith
  have h2 : (1 - 1 / 4096) ^ 2 ≤ (1 - 12 * u * Y) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) h1 2
  have h3 : 25 * u ^ 2 * (1 - 1 / 4096) ^ 2 ≤ 25 * u ^ 2 * (1 - 12 * u * Y) ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hu0 : 0 < u ^ 2 := by positivity
  nlinarith

theorem chart_bound_aux {u r X Y : ℝ} (hu : 0 < u) (hu1 : 1024 * u ≤ 1) (hX : |X| < 1)
    (hY : |Y| < 1) {m : ℝ} (hm0 : 0 ≤ m) (hm : m < r)
    (hN : m ^ 2 * ((1 - 12 * u * Y) ^ 2 + (12 * u * X) ^ 2) = X ^ 2 + (Y - 12 * u) ^ 2) :
    X ^ 2 + (Y - 12 * u) ^ 2 < 33 / 32 * r ^ 2 := by
  have hX' := abs_lt.1 hX
  have hY' := abs_lt.1 hY
  have hD : (1 - 12 * u * Y) ^ 2 + (12 * u * X) ^ 2 ≤ 33 / 32 := by
    have h1 : (1 - 12 * u * Y) ^ 2 ≤ (1 + 12 * u) ^ 2 := by
      apply sq_le_sq'
      · nlinarith
      · nlinarith
    have h2 : (12 * u * X) ^ 2 ≤ (12 * u) ^ 2 := by
      rw [mul_pow, mul_pow]
      have : X ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg u]
    nlinarith
  have hD0 : 0 ≤ (1 - 12 * u * Y) ^ 2 + (12 * u * X) ^ 2 := by positivity
  have hmr : m ^ 2 < r ^ 2 := by nlinarith
  rw [← hN]
  rcases hD0.lt_or_eq with hD1 | hD1
  · calc m ^ 2 * ((1 - 12 * u * Y) ^ 2 + (12 * u * X) ^ 2)
        < r ^ 2 * ((1 - 12 * u * Y) ^ 2 + (12 * u * X) ^ 2) :=
          mul_lt_mul_of_pos_right hmr hD1
      _ ≤ r ^ 2 * (33 / 32) := mul_le_mul_of_nonneg_left hD (sq_nonneg r)
      _ = 33 / 32 * r ^ 2 := by ring
  · rw [← hD1, mul_zero]
    have : 0 < r := lt_of_le_of_lt hm0 hm
    positivity

theorem third_lt_norm_mob {τ u : ℝ} {Z : ℂ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hu : 0 < u)
    (hτu : 1024 * u ≤ τ) (hX : |Z.re| < 7 * u) (hY : |Z.im| < 19 * u) :
    τ / 3 < ‖mob (τ : ℂ) Z‖ := by
  have hX' := abs_lt.1 hX
  have hY' := abs_lt.1 hY
  have hu1 : 1024 * u ≤ 1 := by linarith
  have hD0 : 0 < 1 - τ * Z.re := by nlinarith
  have hne : 1 - (τ : ℂ) * Z ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      zero_re] at this
    linarith
  have hsq := norm_mob_ofReal_sq hne
  set D := (1 - τ * Z.re) ^ 2 + τ ^ 2 * Z.im ^ 2
  have hD : D ≤ 1 + 1 / 50 := by
    have h1 : (1 - τ * Z.re) ^ 2 ≤ (1 + 7 * u) ^ 2 := by
      apply sq_le_sq' <;> nlinarith
    have h2 : τ ^ 2 * Z.im ^ 2 ≤ 361 * u ^ 2 := by
      have : Z.im ^ 2 ≤ 361 * u ^ 2 := by nlinarith
      have : τ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg Z.im]
    nlinarith
  have hN : (τ - 7 * u) ^ 2 ≤ (Z.re - τ) ^ 2 + Z.im ^ 2 := by
    have : (τ - 7 * u) ^ 2 ≤ (τ - Z.re) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    nlinarith [sq_nonneg Z.im]
  have hτ7 : 49 / 50 * τ ^ 2 ≤ (τ - 7 * u) ^ 2 := by nlinarith
  by_contra hc
  push Not at hc
  have hm := norm_nonneg (mob (τ : ℂ) Z)
  have h3 : ‖mob (τ : ℂ) Z‖ ^ 2 ≤ (τ / 3) ^ 2 := pow_le_pow_left₀ hm hc 2
  have hD0' : 0 ≤ D := by positivity
  have h4 : ‖mob (τ : ℂ) Z‖ ^ 2 * D ≤ (τ / 3) ^ 2 * (1 + 1 / 50) :=
    mul_le_mul h3 hD hD0' (by positivity)
  nlinarith

variable (σ : CompactShape)

def tauMin : ℝ := min (tauOne σ) (tauTwo σ)

def cofMin : ℝ := min (1 - tauOne σ ^ 2) (1 - tauTwo σ ^ 2)

def sinMin : ℝ := min (Real.sin σ.θ₁) (Real.sin σ.θ₂)

def layoutScale : ℝ := min (tauMin σ * cofMin σ * sinMin σ) (tauThree σ)

def outerEnd : ℝ := min (tauThree σ / 2) (1 / 5)

def hypLayout : HypLayout where
  g := tauMin σ / 4
  a := tauMin σ / 3
  b := tauMin σ / 2
  e := layoutScale σ / 1024
  β := layoutScale σ / 64
  β' := layoutScale σ / 32
  g₃ := outerEnd σ / 4
  a₃ := outerEnd σ / 2
  b₃ := outerEnd σ

def pChart (z : ℂ) : ℂ := mob (tauTwo σ : ℂ) (σ.rotTwo z)

def pChartInv (w : ℂ) : ℂ :=
  mobInv σ.vertexTwo (-(exp (-((σ.θ₂ : ℂ) * I)) * mobInv (tauTwo σ : ℂ) w))

def coreUnit : ℝ := layoutScale σ / 1024

def hypCoreChartCenter : ℂ := ((12 * coreUnit σ : ℝ) : ℂ) * I

def hypCoreCenter : ℂ := pChartInv σ (hypCoreChartCenter σ)

def hypCoreRadius : ℝ := 6 * coreUnit σ

def hypCoreMargin : ℝ := coreUnit σ

variable {σ}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem tauMin_pos : 0 < tauMin σ := lt_min (tauOne_pos h) (tauTwo_pos h)

omit h in
theorem tauMin_le_one : tauMin σ ≤ tauOne σ := min_le_left _ _

omit h in
theorem tauMin_le_two : tauMin σ ≤ tauTwo σ := min_le_right _ _

theorem cofMin_pos : 0 < cofMin σ := by
  have h1 := tauOne_lt_one (σ := σ)
  have h2 := tauTwo_lt_one (σ := σ)
  have := tauOne_pos h
  have := tauTwo_pos h
  exact lt_min (by nlinarith) (by nlinarith)

omit h in
theorem sinMin_pos : 0 < sinMin σ :=
  lt_min (sin_pos_of_le (θ₁_pos σ) (θ₁_le σ)) (sin_pos_of_le (θ₂_pos σ) (θ₂_le σ))

omit h in
theorem sinMin_le_one' : sinMin σ ≤ 1 := le_trans (min_le_left _ _) (Real.sin_le_one _)

omit h in
theorem cofMin_le_one' : cofMin σ ≤ 1 :=
  le_trans (min_le_left _ _) (by nlinarith [sq_nonneg (tauOne σ)])

theorem layoutScale_pos : 0 < layoutScale σ := by
  have := tauMin_pos h
  have := cofMin_pos h
  have := sinMin_pos (σ := σ)
  exact lt_min (by positivity) (tauThree_pos h)

omit h in
theorem layoutScale_le_tauThree : layoutScale σ ≤ tauThree σ := min_le_right _ _

omit h in
theorem layoutScale_le_prod : layoutScale σ ≤ tauMin σ * cofMin σ * sinMin σ := min_le_left _ _

theorem layoutScale_le_cof_one : layoutScale σ ≤ tauOne σ * (1 - tauOne σ ^ 2) := by
  have hm := layoutScale_le_prod (σ := σ)
  have h1 := tauMin_pos h
  have h2 := cofMin_pos h
  have h3 := sinMin_pos (σ := σ)
  have hc : tauMin σ * cofMin σ * sinMin σ ≤ tauMin σ * cofMin σ :=
    mul_le_of_le_one_right (by positivity) sinMin_le_one'
  have : tauMin σ * cofMin σ ≤ tauOne σ * (1 - tauOne σ ^ 2) :=
    mul_le_mul tauMin_le_one (min_le_left _ _) h2.le (tauOne_pos h).le
  exact le_trans hm (le_trans hc this)

theorem layoutScale_le_cof_two : layoutScale σ ≤ tauTwo σ * (1 - tauTwo σ ^ 2) := by
  have hm := layoutScale_le_prod (σ := σ)
  have h1 := tauMin_pos h
  have h2 := cofMin_pos h
  have h3 := sinMin_pos (σ := σ)
  have hc : tauMin σ * cofMin σ * sinMin σ ≤ tauMin σ * cofMin σ :=
    mul_le_of_le_one_right (by positivity) sinMin_le_one'
  have : tauMin σ * cofMin σ ≤ tauTwo σ * (1 - tauTwo σ ^ 2) :=
    mul_le_mul tauMin_le_two (min_le_right _ _) h2.le (tauTwo_pos h).le
  exact le_trans hm (le_trans hc this)

theorem layoutScale_le_sin_one : layoutScale σ ≤ tauMin σ * Real.sin σ.θ₁ := by
  have hm := layoutScale_le_prod (σ := σ)
  have h1 := tauMin_pos h
  have h2 := cofMin_pos h
  have h3 := sinMin_pos (σ := σ)
  have hc := cofMin_le_one' (σ := σ)
  have : tauMin σ * cofMin σ * sinMin σ ≤ tauMin σ * 1 * Real.sin σ.θ₁ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hc h1.le) (min_le_left _ _) h3.le (by positivity)
  linarith

theorem layoutScale_le_sin_two : layoutScale σ ≤ tauMin σ * Real.sin σ.θ₂ := by
  have hm := layoutScale_le_prod (σ := σ)
  have h1 := tauMin_pos h
  have h2 := cofMin_pos h
  have h3 := sinMin_pos (σ := σ)
  have hc := cofMin_le_one' (σ := σ)
  have : tauMin σ * cofMin σ * sinMin σ ≤ tauMin σ * 1 * Real.sin σ.θ₂ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hc h1.le) (min_le_right _ _) h3.le (by positivity)
  linarith

omit h in
theorem layoutScale_lt_one : layoutScale σ < 1 :=
  lt_of_le_of_lt layoutScale_le_tauThree tauThree_lt_one

theorem outerEnd_pos : 0 < outerEnd σ := lt_min (by linarith [tauThree_pos h]) (by norm_num)

theorem hypLayout_params :
    0 < (hypLayout σ).g ∧ (hypLayout σ).g < (hypLayout σ).a ∧
      (hypLayout σ).a < (hypLayout σ).b ∧ (hypLayout σ).b < 1 ∧ 0 < (hypLayout σ).e ∧
      canonForm (tauOne σ) (hypLayout σ).b < -(hypLayout σ).e ∧
      canonForm (tauTwo σ) (hypLayout σ).b < -(hypLayout σ).e ∧
      0 < (hypLayout σ).β ∧ (hypLayout σ).β < (hypLayout σ).β' ∧
      (hypLayout σ).β' < (hypLayout σ).a * Real.sin σ.θ₁ ∧
      (hypLayout σ).β' < (hypLayout σ).a * Real.sin σ.θ₂ ∧
      0 < (hypLayout σ).g₃ ∧ (hypLayout σ).g₃ < (hypLayout σ).a₃ ∧
      (hypLayout σ).a₃ < (hypLayout σ).b₃ ∧ (hypLayout σ).b₃ < tauThree σ ∧
      (hypLayout σ).b₃ ≤ 1 / 5 := by
  have hm := tauMin_pos h
  have hμ := layoutScale_pos h
  have hm1 : tauMin σ < 1 := lt_of_le_of_lt tauMin_le_one tauOne_lt_one
  have hs1 := layoutScale_le_sin_one h
  have hs2 := layoutScale_le_sin_two h
  have hc1 := layoutScale_le_cof_one h
  have hc2 := layoutScale_le_cof_two h
  have ho := outerEnd_pos h
  have hτ3 := tauThree_pos h
  have hsin1 := sin_pos_of_le (θ₁_pos σ) (θ₁_le σ)
  have hsin1' := Real.sin_le_one σ.θ₁
  have hsin2' := Real.sin_le_one σ.θ₂
  have hsin2 := sin_pos_of_le (θ₂_pos σ) (θ₂_le σ)
  have ht1 := tauOne_pos h
  have ht2 := tauTwo_pos h
  have hx1 : tauOne σ * (1 - tauOne σ ^ 2) ≤ tauOne σ :=
    mul_le_of_le_one_right ht1.le (by nlinarith)
  have hx2 : tauTwo σ * (1 - tauTwo σ ^ 2) ≤ tauTwo σ :=
    mul_le_of_le_one_right ht2.le (by nlinarith)
  simp only [hypLayout] at *
  refine ⟨by positivity, by linarith, by linarith, by linarith, by positivity, ?_, ?_,
    by positivity, by linarith, ?_, ?_, by positivity, by linarith, by linarith, ?_,
    min_le_right _ _⟩
  · exact canonForm_half_lt ht1 tauOne_lt_one (by positivity)
      (by linarith [tauMin_le_one (σ := σ)]) (by positivity) (by nlinarith)
  · exact canonForm_half_lt ht2 tauTwo_lt_one (by positivity)
      (by linarith [tauMin_le_two (σ := σ)]) (by positivity) (by nlinarith)
  · nlinarith
  · nlinarith
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

theorem tauTwo_norm_lt_one : ‖(tauTwo σ : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (tauTwo_pos h)]
  exact tauTwo_lt_one

theorem normSq_tauTwo_ne_one : normSq (tauTwo σ : ℂ) ≠ 1 := by
  rw [Complex.normSq_ofReal]
  have := tauTwo_pos h
  have := tauTwo_lt_one (σ := σ)
  nlinarith

theorem norm_pChart_lt_one {z : ℂ} (hz : ‖z‖ < 1) : ‖pChart σ z‖ < 1 :=
  norm_mob_ofReal_lt_one (tauTwo_pos h) tauTwo_lt_one (norm_rotTwo_lt_one h hz)

theorem rotTwo_eq_mob_pChart {z : ℂ} (hz : ‖z‖ < 1) :
    σ.rotTwo z = mob (-(tauTwo σ : ℂ)) (pChart σ z) := by
  rw [pChart, ← mobInv_eq_mob_neg, mobInv_mob (normSq_tauTwo_ne_one h)
    (one_sub_conj_mul_ne_zero (tauTwo_norm_lt_one h) (norm_rotTwo_lt_one h hz))]

theorem hd_one_eq_pChart {z : ℂ} (hz : ‖z‖ < 1) :
    hd σ 1 z = ‖mob (-(tauTwo σ : ℂ)) (pChart σ z)‖ := by
  rw [← rotTwo_eq_mob_pChart h hz, norm_rotTwo_eq_hd h]

theorem sideOneTwo_comp :
    (sideOneTwo σ - tauTwo σ) / (1 - sideOneTwo σ * tauTwo σ) = tauOne σ := by
  have ho := oplus_tauOne_tauTwo h
  have h1 := tauOne_pos h
  have h2 := tauTwo_pos h
  have h2' := tauTwo_lt_one (σ := σ)
  rw [oplus] at ho
  have hD : 0 < 1 + tauOne σ * tauTwo σ := by positivity
  have hq : 0 < 1 - tauTwo σ ^ 2 := by nlinarith
  have e1 : sideOneTwo σ - tauTwo σ =
      tauOne σ * (1 - tauTwo σ ^ 2) / (1 + tauOne σ * tauTwo σ) := by
    rw [← ho]; field_simp; ring
  have e2 : 1 - sideOneTwo σ * tauTwo σ = (1 - tauTwo σ ^ 2) / (1 + tauOne σ * tauTwo σ) := by
    rw [← ho]; field_simp; ring
  rw [e1, e2]
  field_simp

theorem mob_sideOneTwo_rotTwo {z : ℂ} (hz : ‖z‖ < 1) :
    mob (sideOneTwo σ : ℂ) (σ.rotTwo z) = mob (tauOne σ : ℂ) (pChart σ z) := by
  have hZ := norm_pChart_lt_one h hz
  have ht0 := sideOneTwo_pos h
  have ht1 := sideOneTwo_lt_one h
  have h20 := tauTwo_pos h
  have h21 := tauTwo_lt_one (σ := σ)
  have hab : 1 - sideOneTwo σ * tauTwo σ ≠ 0 := by nlinarith
  have hab' : ((1 - sideOneTwo σ * tauTwo σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hab
  have hc := one_sub_ofReal_mul_ne_zero (tauOne_pos h) tauOne_lt_one hZ
  have hc' : 1 - (((sideOneTwo σ - tauTwo σ) / (1 - sideOneTwo σ * tauTwo σ) : ℝ) : ℂ) *
      pChart σ z ≠ 0 := by
    rw [sideOneTwo_comp h]; exact hc
  have hb : 1 + (tauTwo σ : ℂ) * pChart σ z ≠ 0 := by
    have := one_add_conj_mul_ne_zero (tauTwo_norm_lt_one h) hZ
    rwa [Complex.conj_ofReal] at this
  have e : (1 : ℂ) + tauTwo σ * pChart σ z - sideOneTwo σ * (pChart σ z + tauTwo σ) =
      ((1 - sideOneTwo σ * tauTwo σ : ℝ) : ℂ) *
        (1 - (((sideOneTwo σ - tauTwo σ) / (1 - sideOneTwo σ * tauTwo σ) : ℝ) : ℂ) *
          pChart σ z) := by
    have hr : (1 - sideOneTwo σ * tauTwo σ) *
        ((sideOneTwo σ - tauTwo σ) / (1 - sideOneTwo σ * tauTwo σ)) =
          sideOneTwo σ - tauTwo σ := mul_div_cancel₀ _ hab
    have hkc : ((1 - sideOneTwo σ * tauTwo σ : ℝ) : ℂ) *
        (((sideOneTwo σ - tauTwo σ) / (1 - sideOneTwo σ * tauTwo σ) : ℝ) : ℂ) =
          ((sideOneTwo σ - tauTwo σ : ℝ) : ℂ) := by
      rw [← ofReal_mul, hr]
    rw [mul_sub, mul_one, ← mul_assoc, hkc]
    push_cast
    ring
  have hd : (1 : ℂ) + tauTwo σ * pChart σ z - sideOneTwo σ * (pChart σ z + tauTwo σ) ≠ 0 := by
    rw [e]; exact mul_ne_zero hab' hc'
  rw [rotTwo_eq_mob_pChart h hz, mob_mob_neg_ofReal hb hd hc' hab, sideOneTwo_comp h]

theorem hd_zero_eq_pChart {z : ℂ} (hz : ‖z‖ < 1) :
    hd σ 0 z = ‖mob (tauOne σ : ℂ) (pChart σ z)‖ := by
  rw [← norm_rotOne_eq_hd h, rotOne_eq_mob_rotTwo h hz, norm_mul, norm_neg_exp, one_mul,
    mob_sideOneTwo_rotTwo h hz]

theorem re_mob_tauOne_pChart_nonpos {z : ℂ} (hz : z ∈ σ.triangle) :
    (mob (tauOne σ : ℂ) (pChart σ z)).re ≤ 0 := by
  have hz1 := norm_lt_one_of_mem h hz
  have hs := sector_one h hz
  have hr := re_rot_nonneg (θ₁_pos σ) (θ₁_le σ) hs.1 hs.2
  rw [exp_neg_mul_rotOne h hz1, mob_sideOneTwo_rotTwo h hz1, neg_re] at hr
  linarith

theorem re_mob_neg_tauTwo_pChart_nonneg {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (mob (-(tauTwo σ : ℂ)) (pChart σ z)).re := by
  have hz1 := norm_lt_one_of_mem h hz
  have hs := sector_two h hz
  rw [← rotTwo_eq_mob_pChart h hz1]
  exact re_nonneg_of_sector (θ₂_pos σ) (θ₂_le σ) hs.1 hs.2

theorem im_pChart_nonneg {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ (pChart σ z).im := by
  have hz1 := norm_lt_one_of_mem h hz
  have hW := norm_rotTwo_lt_one h hz1
  have e := im_mob_ofReal (tauTwo σ) (σ.rotTwo z)
  have hN : 0 < normSq (1 - (tauTwo σ : ℂ) * σ.rotTwo z) :=
    normSq_pos.2 (one_sub_ofReal_mul_ne_zero (tauTwo_pos h) tauTwo_lt_one hW)
  have hq : 0 ≤ 1 - tauTwo σ ^ 2 := by nlinarith [tauTwo_pos h, tauTwo_lt_one (σ := σ)]
  have hi := (sector_two h hz).1
  have : 0 ≤ (pChart σ z).im * normSq (1 - (tauTwo σ : ℂ) * σ.rotTwo z) := by
    rw [pChart, e]; exact mul_nonneg hq hi
  exact (mul_nonneg_iff_of_pos_right hN).1 this

theorem lensCoord_eq_pChart {z : ℂ} (hz : ‖z‖ < 1) :
    lensCoord σ z = 2 * (pChart σ z).im / (1 - normSq (pChart σ z)) :=
  (lensForm_mob (tauTwo_pos h) tauTwo_lt_one (norm_rotTwo_lt_one h hz)).symm

theorem coreUnit_pos : 0 < coreUnit σ := by
  have := layoutScale_pos h
  unfold coreUnit; positivity

theorem coreUnit_le_one : 1024 * coreUnit σ ≤ tauOne σ * (1 - tauOne σ ^ 2) := by
  have := layoutScale_le_cof_one h
  unfold coreUnit; linarith

theorem coreUnit_le_two : 1024 * coreUnit σ ≤ tauTwo σ * (1 - tauTwo σ ^ 2) := by
  have := layoutScale_le_cof_two h
  unfold coreUnit; linarith

omit h in
theorem coreUnit_le_three : 1024 * coreUnit σ ≤ tauThree σ := by
  have := layoutScale_le_tauThree (σ := σ)
  unfold coreUnit; linarith

omit h in
theorem coreUnit_small : 1024 * coreUnit σ ≤ 1 := by
  have := layoutScale_lt_one (σ := σ)
  unfold coreUnit; linarith

theorem coreUnit_le_sin_one : 1024 * coreUnit σ ≤ tauOne σ * Real.sin σ.θ₁ := by
  have := layoutScale_le_sin_one h
  have := mul_le_mul_of_nonneg_right (tauMin_le_one (σ := σ))
    (sin_pos_of_le (θ₁_pos σ) (θ₁_le σ)).le
  unfold coreUnit; linarith

theorem coreUnit_le_sin_two : 1024 * coreUnit σ ≤ tauTwo σ * Real.sin σ.θ₂ := by
  have := layoutScale_le_sin_two h
  have := mul_le_mul_of_nonneg_right (tauMin_le_two (σ := σ))
    (sin_pos_of_le (θ₂_pos σ) (θ₂_le σ)).le
  unfold coreUnit; linarith

omit h in
theorem hypLayout_e : (hypLayout σ).e = coreUnit σ := rfl

omit h in
theorem hypLayout_β : (hypLayout σ).β = 16 * coreUnit σ := by
  simp only [hypLayout, coreUnit]; ring

omit h in
theorem hypLayout_β' : (hypLayout σ).β' = 32 * coreUnit σ := by
  simp only [hypLayout, coreUnit]; ring

omit h in
theorem canon_zero_eq (z : ℂ) : canon σ 0 z = canonForm (tauOne σ) (hd σ 0 z) := rfl

omit h in
theorem canon_one_eq (z : ℂ) : canon σ 1 z = canonForm (tauTwo σ) (hd σ 1 z) := rfl

omit h in
theorem canon_two_eq (z : ℂ) : canon σ 2 z = canonForm (tauThree σ) ‖z‖ := rfl

theorem pChart_small {z : ℂ} (hz : z ∈ σ.triangle) (h0 : -coreUnit σ ≤ canon σ 0 z)
    (h1 : -coreUnit σ ≤ canon σ 1 z) (hl : lensCoord σ z ≤ 32 * coreUnit σ) :
    |(pChart σ z).re| ≤ 2 * coreUnit σ ∧ 0 ≤ (pChart σ z).im ∧
      (pChart σ z).im ≤ 16 * coreUnit σ := by
  have hz1 := norm_lt_one_of_mem h hz
  have hZ := norm_pChart_lt_one h hz1
  have hu := coreUnit_pos h
  have hY0 := im_pChart_nonneg h hz
  have hN := normSq_lt_one_of_norm_lt hZ
  have hN0 := normSq_nonneg (pChart σ z)
  rw [lensCoord_eq_pChart h hz1, div_le_iff₀ (by linarith)] at hl
  have hY : (pChart σ z).im ≤ 16 * coreUnit σ := by nlinarith
  refine ⟨abs_le.2 ⟨?_, ?_⟩, hY0, hY⟩
  · have hZ' : ‖-conj (pChart σ z)‖ < 1 := by rwa [norm_neg, Complex.norm_conj]
    have hi : (-conj (pChart σ z)).im = (pChart σ z).im := by simp
    have := small_of_mob (tauTwo_pos h) tauTwo_lt_one hu (coreUnit_le_two h) hZ'
      (by rw [hi]; exact hY0) (by rw [hi]; exact hY)
      (by rw [norm_mob_ofReal_neg_conj, ← hd_one_eq_pChart h hz1]; exact h1)
      (by rw [re_mob_ofReal_neg_conj]; linarith [re_mob_neg_tauTwo_pChart_nonneg h hz])
    have hr : (-conj (pChart σ z)).re = -(pChart σ z).re := by simp
    linarith
  · exact small_of_mob (tauOne_pos h) tauOne_lt_one hu (coreUnit_le_one h) hZ hY0 hY
      (by rw [← hd_zero_eq_pChart h hz1]; exact h0) (re_mob_tauOne_pChart_nonpos h hz)

theorem canon_zero_le_norm_pChart {z : ℂ} (hz : ‖z‖ < 1) : canon σ 0 z ≤ ‖pChart σ z‖ := by
  have hZ := norm_pChart_lt_one h hz
  rw [canon_zero_eq, hd_zero_eq_pChart h hz]
  exact canonForm_le_of_triangle (tauOne_pos h).le tauOne_lt_one
    (norm_mob_ofReal_lt_one (tauOne_pos h) tauOne_lt_one hZ)
    (pseudo_triangle (tauOne_pos h).le tauOne_lt_one hZ)

theorem canon_one_le_norm_pChart {z : ℂ} (hz : ‖z‖ < 1) : canon σ 1 z ≤ ‖pChart σ z‖ := by
  have hZ := norm_pChart_lt_one h hz
  have hZ' : ‖-conj (pChart σ z)‖ < 1 := by rwa [norm_neg, Complex.norm_conj]
  have hn : ‖-conj (pChart σ z)‖ = ‖pChart σ z‖ := by rw [norm_neg, Complex.norm_conj]
  rw [canon_one_eq, hd_one_eq_pChart h hz, ← norm_mob_ofReal_neg_conj, ← hn]
  exact canonForm_le_of_triangle (tauTwo_pos h).le tauTwo_lt_one
    (norm_mob_ofReal_lt_one (tauTwo_pos h) tauTwo_lt_one hZ')
    (pseudo_triangle (tauTwo_pos h).le tauTwo_lt_one hZ')

theorem norm_ge_of_pChart {z : ℂ} (hz : z ∈ σ.triangle) :
    tauThree σ - ‖pChart σ z‖ ≤ ‖z‖ := by
  have hz1 := norm_lt_one_of_mem h hz
  have hs := canon_zero_add_two_nonneg h hz
  have hc := canon_zero_le_norm_pChart h hz1
  rw [canon_two_eq] at hs
  exact ge_of_canonForm (tauThree_pos h).le tauThree_lt_one (norm_nonneg z) hz1
    (norm_nonneg _) (by linarith)

theorem norm_pChartInv_aux {w : ℂ} (hw : ‖w‖ < 1) :
    ‖-(exp (-((σ.θ₂ : ℂ) * I)) * mobInv (tauTwo σ : ℂ) w)‖ < 1 := by
  rw [norm_neg, norm_mul, norm_exp_neg_ofReal_mul_I, one_mul]
  exact norm_mobInv_lt_one (tauTwo_norm_lt_one h) hw

theorem norm_pChartInv_lt_one {w : ℂ} (hw : ‖w‖ < 1) : ‖pChartInv σ w‖ < 1 :=
  norm_mobInv_lt_one (norm_vertexTwo_lt_one h) (norm_pChartInv_aux h hw)

theorem pChart_pChartInv {w : ℂ} (hw : ‖w‖ < 1) : pChart σ (pChartInv σ w) = w := by
  have hy := norm_pChartInv_aux h hw
  rw [pChart, rotTwo_eq_mul_mob h, pChartInv, mob_mobInv (normSq_vertexTwo_ne_one h)
    (one_add_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hy)]
  rw [show -exp ((σ.θ₂ : ℂ) * I) * -(exp (-((σ.θ₂ : ℂ) * I)) * mobInv (tauTwo σ : ℂ) w) =
      (exp ((σ.θ₂ : ℂ) * I) * exp (-((σ.θ₂ : ℂ) * I))) * mobInv (tauTwo σ : ℂ) w by ring,
    exp_mul_exp_neg, one_mul]
  exact mob_mobInv (normSq_tauTwo_ne_one h)
    (one_add_conj_mul_ne_zero (tauTwo_norm_lt_one h) hw)

theorem pChartInv_pChart {z : ℂ} (hz : ‖z‖ < 1) : pChartInv σ (pChart σ z) = z := by
  have hW := norm_rotTwo_lt_one h hz
  rw [pChartInv, pChart, mobInv_mob (normSq_tauTwo_ne_one h)
    (one_sub_conj_mul_ne_zero (tauTwo_norm_lt_one h) hW), exp_neg_mul_rotTwo h, neg_neg]
  exact mobInv_mob (normSq_vertexTwo_ne_one h)
    (one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz)

theorem norm_mob_pChart {p z : ℂ} (hp : ‖p‖ < 1) (hz : ‖z‖ < 1) :
    ‖mob (pChart σ p) (pChart σ z)‖ = ‖mob p z‖ := by
  have hp' := norm_rotTwo_lt_one h hp
  have hz' := norm_rotTwo_lt_one h hz
  rw [pChart, pChart, norm_mob_mob_mob (normSq_tauTwo_ne_one h)
    (one_sub_conj_mul_ne_zero (tauTwo_norm_lt_one h) hp')
    (one_sub_conj_mul_ne_zero (tauTwo_norm_lt_one h) hz')
    (one_sub_conj_mul_ne_zero hp' hz'), rotTwo_eq_mul_mob h, rotTwo_eq_mul_mob h,
    mob_mul_mul (norm_neg_exp _), norm_mul, norm_neg_exp, one_mul]
  have hv := norm_vertexTwo_lt_one h
  exact norm_mob_mob_mob (normSq_vertexTwo_ne_one h) (one_sub_conj_mul_ne_zero hv hp)
    (one_sub_conj_mul_ne_zero hv hz) (one_sub_conj_mul_ne_zero hp hz)

theorem norm_hypCoreChartCenter : ‖hypCoreChartCenter σ‖ = 12 * coreUnit σ := by
  have := coreUnit_pos h
  rw [hypCoreChartCenter, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem norm_hypCoreChartCenter_lt_one : ‖hypCoreChartCenter σ‖ < 1 := by
  rw [norm_hypCoreChartCenter h]
  have := coreUnit_small (σ := σ)
  linarith [coreUnit_pos h]

theorem norm_mob_hypCoreCenter {z : ℂ} (hz : ‖z‖ < 1) :
    ‖mob (hypCoreCenter σ) z‖ = ‖mob (hypCoreChartCenter σ) (pChart σ z)‖ := by
  have hc := norm_hypCoreChartCenter_lt_one h
  rw [hypCoreCenter, ← norm_mob_pChart h (norm_pChartInv_lt_one h hc) hz,
    pChart_pChartInv h hc]

theorem norm_hypCoreCenter_lt_one : ‖hypCoreCenter σ‖ < 1 :=
  norm_pChartInv_lt_one h (norm_hypCoreChartCenter_lt_one h)

theorem chart_sq_hypCore {z : ℂ} (hz : ‖z‖ < 1) :
    ‖mob (hypCoreCenter σ) z‖ ^ 2 * ((1 - 12 * coreUnit σ * (pChart σ z).im) ^ 2 +
      (12 * coreUnit σ * (pChart σ z).re) ^ 2) =
      (pChart σ z).re ^ 2 + ((pChart σ z).im - 12 * coreUnit σ) ^ 2 := by
  have hu := coreUnit_pos h
  have hk : |12 * coreUnit σ| < 1 := by
    rw [abs_of_pos (by positivity)]; linarith [coreUnit_small (σ := σ)]
  rw [norm_mob_hypCoreCenter h hz]
  exact norm_mob_I_sq hk (norm_pChart_lt_one h hz)

theorem hypCore_params : 0 < hypCoreMargin σ ∧ hypCoreMargin σ < hypCoreRadius σ ∧
    hypCoreRadius σ + hypCoreMargin σ < 1 := by
  have hu := coreUnit_pos h
  have := coreUnit_small (σ := σ)
  unfold hypCoreMargin hypCoreRadius
  refine ⟨hu, by linarith, by linarith⟩

theorem window_mem_core {z : ℂ} (hz : z ∈ σ.triangle) (h0 : -(hypLayout σ).e ≤ canon σ 0 z)
    (h1 : -(hypLayout σ).e ≤ canon σ 1 z) (hlo : (hypLayout σ).β ≤ lensCoord σ z)
    (hhi : lensCoord σ z ≤ (hypLayout σ).β') :
    ‖mob (hypCoreCenter σ) z‖ < hypCoreRadius σ - hypCoreMargin σ := by
  have hz1 := norm_lt_one_of_mem h hz
  have hZ := norm_pChart_lt_one h hz1
  have hu := coreUnit_pos h
  have hu1 := coreUnit_small (σ := σ)
  rw [hypLayout_e] at h0 h1
  rw [hypLayout_β'] at hhi
  rw [hypLayout_β] at hlo
  obtain ⟨hX, hY0, hY⟩ := pChart_small h hz h0 h1 hhi
  have hN := normSq_lt_one_of_norm_lt hZ
  rw [lensCoord_eq_pChart h hz1, le_div_iff₀ (by linarith)] at hlo
  have hns : normSq (pChart σ z) = (pChart σ z).re ^ 2 + (pChart σ z).im ^ 2 := by
    rw [normSq_apply]; ring
  rw [hns] at hlo
  have hlo' : 8 * coreUnit σ * (1 - ((pChart σ z).re ^ 2 + (pChart σ z).im ^ 2)) ≤
      (pChart σ z).im := by linarith
  have hw := window_aux hu hu1 hX hY0 hY hlo'
  have hsq := chart_sq_hypCore h hz1
  set D := (1 - 12 * coreUnit σ * (pChart σ z).im) ^ 2 + (12 * coreUnit σ * (pChart σ z).re) ^ 2
  have hD1 : (1 - 12 * coreUnit σ * (pChart σ z).im) ^ 2 ≤ D := by
    have := sq_nonneg (12 * coreUnit σ * (pChart σ z).re); linarith
  have hD0 : 0 < (1 - 12 * coreUnit σ * (pChart σ z).im) ^ 2 := by
    have : 12 * coreUnit σ * (pChart σ z).im < 1 := by nlinarith
    have : 0 < 1 - 12 * coreUnit σ * (pChart σ z).im := by linarith
    positivity
  have key : ‖mob (hypCoreCenter σ) z‖ ^ 2 < (5 * coreUnit σ) ^ 2 := by
    by_contra hc
    push Not at hc
    have : (5 * coreUnit σ) ^ 2 * D ≤ ‖mob (hypCoreCenter σ) z‖ ^ 2 * D :=
      mul_le_mul_of_nonneg_right hc (by linarith)
    have : 25 * coreUnit σ ^ 2 * (1 - 12 * coreUnit σ * (pChart σ z).im) ^ 2 ≤
        (5 * coreUnit σ) ^ 2 * D := by
      have := mul_le_mul_of_nonneg_left hD1 (by positivity : (0 : ℝ) ≤ (5 * coreUnit σ) ^ 2)
      nlinarith
    linarith
  have h5 : ‖mob (hypCoreCenter σ) z‖ < 5 * coreUnit σ :=
    lt_of_pow_lt_pow_left₀ 2 (by positivity) key
  unfold hypCoreRadius hypCoreMargin
  linarith

theorem core_chart_bound {z : ℂ} (hz : ‖z‖ < 1) {r : ℝ}
    (hc : ‖mob (hypCoreCenter σ) z‖ < r) :
    (pChart σ z).re ^ 2 + ((pChart σ z).im - 12 * coreUnit σ) ^ 2 < 33 / 32 * r ^ 2 := by
  have hZ := norm_pChart_lt_one h hz
  exact chart_bound_aux (coreUnit_pos h) coreUnit_small
    (lt_of_le_of_lt (Complex.abs_re_le_norm _) hZ) (lt_of_le_of_lt (Complex.abs_im_le_norm _) hZ)
    (norm_nonneg _) hc (chart_sq_hypCore h hz)

theorem core_bounds_seven {z : ℂ} (hz : ‖z‖ < 1)
    (hc : ‖mob (hypCoreCenter σ) z‖ < hypCoreRadius σ + hypCoreMargin σ) :
    |(pChart σ z).re| < 8 * coreUnit σ ∧ 4 * coreUnit σ < (pChart σ z).im ∧
      (pChart σ z).im < 20 * coreUnit σ := by
  have hu := coreUnit_pos h
  have hb := core_chart_bound h hz hc
  have hr : hypCoreRadius σ + hypCoreMargin σ = 7 * coreUnit σ := by
    unfold hypCoreRadius hypCoreMargin; ring
  rw [hr] at hb
  have hX : |(pChart σ z).re| < 8 * coreUnit σ := by
    rw [← abs_of_pos (by positivity : 0 < 8 * coreUnit σ)]
    apply sq_lt_sq.1
    nlinarith [sq_nonneg ((pChart σ z).im - 12 * coreUnit σ)]
  refine ⟨hX, ?_, ?_⟩ <;> nlinarith [sq_nonneg (pChart σ z).re]

theorem wallSide_two_pos_of_chart {z : ℂ} (hz : ‖z‖ < 1) (hY : 0 < (pChart σ z).im) :
    0 < σ.wallSide 2 z := by
  have hZ := norm_pChart_lt_one h hz
  have h20 := tauTwo_pos h
  have h21 := tauTwo_lt_one (σ := σ)
  rw [CompactShape.wallSide_two_eq, rotTwo_eq_mob_pChart h hz]
  have e := im_mob_ofReal (-tauTwo σ) (pChart σ z)
  push_cast at e
  have hne : (1 : ℂ) - -(tauTwo σ : ℂ) * pChart σ z ≠ 0 := by
    have := one_add_conj_mul_ne_zero (tauTwo_norm_lt_one h) hZ
    rw [Complex.conj_ofReal] at this
    intro h0; apply this; linear_combination h0
  have hN := normSq_pos.2 hne
  have hq : 0 < (1 - (-tauTwo σ) ^ 2) * (pChart σ z).im :=
    mul_pos (by nlinarith) hY
  have him : 0 < (mob (-(tauTwo σ : ℂ)) (pChart σ z)).im := by
    by_contra hn
    push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg hn hN.le
    linarith
  have hN2 : 0 < normSq (1 - σ.eps * conj σ.vertexTwo * z) := by
    rw [CompactShape.eps_hyp h]
    apply normSq_pos.2
    simpa using one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz
  exact mul_pos him hN2

omit h in
theorem sin_bound_aux {τ u X Y s c : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hu : 0 < u)
    (hX : |X| < 8 * u) (hY0 : 0 < Y) (hY : Y < 20 * u) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hτs : 1024 * u ≤ τ * s) :
    Y * (1 - τ ^ 2) * c < (τ * (1 + X ^ 2 + Y ^ 2) - |X| * (1 + τ ^ 2)) * s := by
  have hX0 := abs_nonneg X
  have hτ2 : τ ^ 2 ≤ 1 := by nlinarith
  have hk : (1 - τ ^ 2) * c ≤ 1 :=
    le_trans (mul_le_of_le_one_left hc0 (by nlinarith)) hc1
  have hB : Y * (1 - τ ^ 2) * c ≤ Y := by
    rw [mul_assoc]; exact mul_le_of_le_one_right hY0.le hk
  have hA : τ - 16 * u ≤ τ * (1 + X ^ 2 + Y ^ 2) - |X| * (1 + τ ^ 2) := by
    have h1 : |X| * (1 + τ ^ 2) ≤ 16 * u := by
      have := mul_le_mul hX.le (by linarith : 1 + τ ^ 2 ≤ 2) (by positivity) (by positivity)
      linarith
    have h2 : τ ≤ τ * (1 + X ^ 2 + Y ^ 2) := by
      have : 0 ≤ τ * (X ^ 2 + Y ^ 2) := by positivity
      nlinarith
    linarith
  have hA' : (τ - 16 * u) * s ≤ (τ * (1 + X ^ 2 + Y ^ 2) - |X| * (1 + τ ^ 2)) * s :=
    mul_le_mul_of_nonneg_right hA hs0.le
  have h16 : 16 * u * s ≤ 16 * u := mul_le_of_le_one_right (by positivity) hs1
  nlinarith

theorem wallSide_zero_pos_of_chart {z : ℂ} (hz : ‖z‖ < 1)
    (hX : |(pChart σ z).re| < 8 * coreUnit σ) (hY0 : 0 < (pChart σ z).im)
    (hY : (pChart σ z).im < 20 * coreUnit σ) : 0 < σ.wallSide 0 z := by
  have hZ := norm_pChart_lt_one h hz
  have e := rotTwo_rot_im_mul_normSq h z
  have e2 := im_rot_mob_neg σ.θ₂ (tauTwo σ) (pChart σ z)
  rw [← rotTwo_eq_mob_pChart h hz] at e2
  have hk := sin_bound_aux (tauTwo_pos h) tauTwo_lt_one (coreUnit_pos h) hX hY0 hY
    (sin_pos_of_le (θ₂_pos σ) (θ₂_le σ)) (Real.sin_le_one _)
    (cos_nonneg_of_le (θ₂_pos σ) (θ₂_le σ)) (Real.cos_le_one _) (coreUnit_le_sin_two h)
  have hXa : -|(pChart σ z).re| ≤ (pChart σ z).re := neg_abs_le _
  have hs := sin_pos_of_le (θ₂_pos σ) (θ₂_le σ)
  have hm : -|(pChart σ z).re| * (1 + tauTwo σ ^ 2) * Real.sin σ.θ₂ ≤
      (pChart σ z).re * (1 + tauTwo σ ^ 2) * Real.sin σ.θ₂ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hXa (by positivity)) hs.le
  have hne : 1 + (tauTwo σ : ℂ) * pChart σ z ≠ 0 := by
    have := one_add_conj_mul_ne_zero (tauTwo_norm_lt_one h) hZ
    rwa [Complex.conj_ofReal] at this
  have hN := normSq_pos.2 hne
  have hneg : (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im < 0 := by
    by_contra hn
    push Not at hn
    have := mul_nonneg hn hN.le
    linarith
  have hN2 : 0 < normSq (1 - σ.vertexTwo * z) := by
    apply normSq_pos.2
    have := one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz
    rwa [conj_vertexTwo] at this
  have ht := sideTwoThree_lt_one h
  have ht0 := sideTwoThree_pos h
  have hq : 0 < 1 - sideTwoThree σ ^ 2 := by nlinarith
  have h3 := mul_neg_of_neg_of_pos hneg hN2
  rw [e] at h3
  exact pos_of_mul_pos_right (neg_lt_zero.1 h3) hq.le

theorem wallSide_one_pos_of_chart {z : ℂ} (hz : ‖z‖ < 1)
    (hX : |(pChart σ z).re| < 8 * coreUnit σ) (hY0 : 0 < (pChart σ z).im)
    (hY : (pChart σ z).im < 20 * coreUnit σ) : 0 < σ.wallSide 1 z := by
  have hZ := norm_pChart_lt_one h hz
  have e := rotOne_im_mul_normSq h hz
  have e2 := im_rot_mob σ.θ₁ (tauOne σ) (pChart σ z)
  rw [← mob_sideOneTwo_rotTwo h hz, ← rotOne_eq_mob_rotTwo h hz] at e2
  have hk := sin_bound_aux (tauOne_pos h) tauOne_lt_one (coreUnit_pos h) hX hY0 hY
    (sin_pos_of_le (θ₁_pos σ) (θ₁_le σ)) (Real.sin_le_one _)
    (cos_nonneg_of_le (θ₁_pos σ) (θ₁_le σ)) (Real.cos_le_one _) (coreUnit_le_sin_one h)
  have hXa : (pChart σ z).re ≤ |(pChart σ z).re| := le_abs_self _
  have hs := sin_pos_of_le (θ₁_pos σ) (θ₁_le σ)
  have hm : (pChart σ z).re * (1 + tauOne σ ^ 2) * Real.sin σ.θ₁ ≤
      |(pChart σ z).re| * (1 + tauOne σ ^ 2) * Real.sin σ.θ₁ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hXa (by positivity)) hs.le
  have hne := one_sub_ofReal_mul_ne_zero (tauOne_pos h) tauOne_lt_one hZ
  have hN := normSq_pos.2 hne
  have hpos : 0 < (σ.rotOne z).im := by
    by_contra hn
    push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg hn hN.le
    linarith
  have hN2 : 0 < normSq (1 - conj σ.vertexOne * z) :=
    normSq_pos.2 (one_sub_conj_mul_ne_zero (norm_vertexOne_lt_one h) hz)
  have ht := sideOneThree_lt_one h
  have ht0 := sideOneThree_pos h
  have hq : 0 < 1 - sideOneThree σ ^ 2 := by nlinarith
  have h3 := mul_pos hpos hN2
  rw [e] at h3
  exact pos_of_mul_pos_right h3 hq.le

theorem mem_openTriangle_of_core {z : ℂ} (hz : ‖z‖ < 1)
    (hc : ‖mob (hypCoreCenter σ) z‖ < hypCoreRadius σ + hypCoreMargin σ) :
    z ∈ σ.triangle ∧ ∀ i, 0 < σ.wallSide i z := by
  obtain ⟨hX, hYl, hYu⟩ := core_bounds_seven h hz hc
  have hY0 : 0 < (pChart σ z).im := lt_trans (by linarith [coreUnit_pos h]) hYl
  have hall : ∀ i, 0 < σ.wallSide i z := by
    intro i
    fin_cases i
    · exact wallSide_zero_pos_of_chart h hz hX hY0 hYu
    · exact wallSide_one_pos_of_chart h hz hX hY0 hYu
    · exact wallSide_two_pos_of_chart h hz hY0
  refine ⟨⟨?_, fun i => (hall i).le⟩, hall⟩
  rw [CompactShape.plane_hyp h, Metric.mem_ball, dist_zero_right]
  exact hz

theorem core_separation {z : ℂ} (hz : ‖z‖ < 1) (hc : ‖mob (hypCoreCenter σ) z‖ < hypCoreRadius σ) :
    (hypLayout σ).a < hd σ 0 z ∧ (hypLayout σ).a < hd σ 1 z ∧
      (hypLayout σ).β / 2 < lensCoord σ z ∧ lensCoord σ z < 2 * (hypLayout σ).β' ∧
      (hypLayout σ).b₃ < ‖z‖ := by
  have hu := coreUnit_pos h
  have hu1 := coreUnit_small (σ := σ)
  have hb := core_chart_bound h hz hc
  have hZ := norm_pChart_lt_one h hz
  have hm := (hypCore_params h).1
  have hT := (mem_openTriangle_of_core h hz (by linarith)).1
  set X := (pChart σ z).re with hXdef
  set Y := (pChart σ z).im with hYdef
  have hr : hypCoreRadius σ = 6 * coreUnit σ := rfl
  rw [hr] at hb
  have hX : |X| < 7 * coreUnit σ := by
    rw [← abs_of_pos (by positivity : 0 < 7 * coreUnit σ)]
    apply sq_lt_sq.1
    nlinarith [sq_nonneg (Y - 12 * coreUnit σ)]
  have hX' := abs_lt.1 hX
  have hYl : 5 * coreUnit σ < Y := by nlinarith [sq_nonneg X]
  have hYu : Y < 19 * coreUnit σ := by nlinarith [sq_nonneg X]
  have hY : |Y| < 19 * coreUnit σ := abs_lt.2 ⟨by linarith, hYu⟩
  have h1 := coreUnit_le_one h
  have h2 := coreUnit_le_two h
  have hx1 : tauOne σ * (1 - tauOne σ ^ 2) ≤ tauOne σ :=
    mul_le_of_le_one_right (tauOne_pos h).le (by nlinarith [tauOne_pos h])
  have hx2 : tauTwo σ * (1 - tauTwo σ ^ 2) ≤ tauTwo σ :=
    mul_le_of_le_one_right (tauTwo_pos h).le (by nlinarith [tauTwo_pos h])
  have hns : normSq (pChart σ z) = X ^ 2 + Y ^ 2 := by rw [normSq_apply]; ring
  have hnZ : X ^ 2 + Y ^ 2 < 410 * coreUnit σ ^ 2 := by
    have : X ^ 2 < 49 * coreUnit σ ^ 2 := by
      have := sq_lt_sq' hX'.1 hX'.2; linarith
    have : Y ^ 2 < 361 * coreUnit σ ^ 2 := by
      have := sq_lt_sq' (by linarith : -(19 * coreUnit σ) < Y) hYu; linarith
    linarith
  have hsmall : 410 * coreUnit σ ^ 2 ≤ 1 / 1000 := by nlinarith
  have hlens : lensCoord σ z = 2 * Y / (1 - (X ^ 2 + Y ^ 2)) := by
    rw [lensCoord_eq_pChart h hz, hns]
  have hden : 0 < 1 - (X ^ 2 + Y ^ 2) := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hd_zero_eq_pChart h hz]
    have := third_lt_norm_mob (tauOne_pos h) tauOne_lt_one hu (by linarith) hX hY
    simp only [hypLayout]
    linarith [tauMin_le_one (σ := σ)]
  · rw [hd_one_eq_pChart h hz, ← norm_mob_ofReal_neg_conj]
    have := third_lt_norm_mob (Z := -conj (pChart σ z)) (tauTwo_pos h) tauTwo_lt_one hu
      (by linarith) (by simpa using hX) (by simpa using hY)
    simp only [hypLayout]
    linarith [tauMin_le_two (σ := σ)]
  · rw [hlens, hypLayout_β, lt_div_iff₀ hden]
    nlinarith
  · rw [hlens, hypLayout_β', div_lt_iff₀ hden]
    nlinarith
  · have hng := norm_ge_of_pChart h hT
    have hZn : ‖pChart σ z‖ < 21 * coreUnit σ := by
      have h0 : ‖pChart σ z‖ ^ 2 < (21 * coreUnit σ) ^ 2 := by
        rw [Complex.sq_norm, hns]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h0
    have h3 := coreUnit_le_three (σ := σ)
    have : (hypLayout σ).b₃ ≤ tauThree σ / 2 := min_le_left _ _
    linarith

theorem norm_gt_of_lensRegion {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : -(hypLayout σ).e ≤ canon σ 0 z) (h1 : -(hypLayout σ).e ≤ canon σ 1 z)
    (hl : lensCoord σ z ≤ (hypLayout σ).β') : (hypLayout σ).b₃ < ‖z‖ := by
  have hu := coreUnit_pos h
  rw [hypLayout_e] at h0 h1
  rw [hypLayout_β'] at hl
  obtain ⟨hX, hY0, hY⟩ := pChart_small h hz h0 h1 hl
  have hX' := abs_le.1 hX
  have hZn : ‖pChart σ z‖ < 17 * coreUnit σ := by
    have h0 : ‖pChart σ z‖ ^ 2 < (17 * coreUnit σ) ^ 2 := by
      rw [Complex.sq_norm, normSq_apply]
      have : (pChart σ z).re ^ 2 ≤ (2 * coreUnit σ) ^ 2 := sq_le_sq' hX'.1 hX'.2
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h0
  have hng := norm_ge_of_pChart h hz
  have h3 := coreUnit_le_three (σ := σ)
  have : (hypLayout σ).b₃ ≤ tauThree σ / 2 := min_le_left _ _
  linarith

end Hyp

end HypFold

end GC.Seifert
