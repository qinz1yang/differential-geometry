import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open scoped BigOperators

namespace DifferentialGeometry.Analysis

theorem norm_sq_add_le {V : Type*} [SeminormedAddCommGroup V] (a b : V) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have hab := norm_add_le a b
  nlinarith only [hab, norm_nonneg a, norm_nonneg b, norm_nonneg (a + b),
    sq_nonneg (‖a‖ - ‖b‖)]

theorem norm_sq_sub_le {V : Type*} [SeminormedAddCommGroup V] (a b : V) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have hab := norm_sub_le a b
  nlinarith only [hab, norm_nonneg a, norm_nonneg b, norm_nonneg (a - b),
    sq_nonneg (‖a‖ - ‖b‖)]

theorem norm_add_sub_sub_sub_sub_le {V : Type*} [SeminormedAddCommGroup V]
    (b1 b2 b3 b4 b5 b6 : V) :
    ‖b1 + b2 - b3 - b4 - b5 - b6‖ ≤
      ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by
  calc
    ‖b1 + b2 - b3 - b4 - b5 - b6‖
        ≤ ‖b1 + b2 - b3 - b4 - b5‖ + ‖b6‖ := norm_sub_le _ _
    _ ≤ (‖b1 + b2 - b3 - b4‖ + ‖b5‖) + ‖b6‖ := by
      have := norm_sub_le (b1 + b2 - b3 - b4) b5
      linarith
    _ ≤ ((‖b1 + b2 - b3‖ + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
      have := norm_sub_le (b1 + b2 - b3) b4
      linarith
    _ ≤ (((‖b1 + b2‖ + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
      have := norm_sub_le (b1 + b2) b3
      linarith
    _ ≤ ((((‖b1‖ + ‖b2‖) + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
      have := norm_add_le b1 b2
      linarith
    _ = ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by ring

theorem le_sq_of_sqrt_le {r c : ℝ} (hr : 0 ≤ r) (h : Real.sqrt r ≤ c) :
    r ≤ c ^ 2 := by
  simpa [Real.sq_sqrt hr] using pow_le_pow_left₀ (Real.sqrt_nonneg r) h 2

theorem mul_three_le_mul_three {a b c A B C : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haA : a ≤ A) (hbB : b ≤ B) (hcC : c ≤ C) :
    a * b * c ≤ A * B * C :=
  mul_le_mul (mul_le_mul haA hbB hb hA) hcC hc (mul_nonneg hA hB)

theorem sq_add_sq_le_sq_add_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [mul_nonneg ha hb]

theorem three_term_sq_le_weighted_product {b0 b1 a p u d : ℝ}
    (hp1 : (1 : ℝ) ≤ p) (hpa : a ^ 2 ≤ p)
    (hu : 0 ≤ u) (hd : d ^ 2 ≤ u) :
    (b0 * d + b1 * d + b1 * a * d) ^ 2 ≤
      (2 * (b0 + b1) ^ 2 + 2 * b1 ^ 2) * (p * u) := by
  have hp : (0 : ℝ) ≤ p := zero_le_one.trans hp1
  have hdu : d ^ 2 ≤ p * u := by
    calc
      d ^ 2 ≤ u := hd
      _ = 1 * u := (one_mul u).symm
      _ ≤ p * u := mul_le_mul_of_nonneg_right hp1 hu
  have had : a ^ 2 * d ^ 2 ≤ p * u := by
    exact (mul_le_mul_of_nonneg_right hpa (sq_nonneg d)).trans
      (mul_le_mul_of_nonneg_left hd hp)
  have hstep : (b0 * d + b1 * d + b1 * a * d) ^ 2 ≤
      2 * (b0 + b1) ^ 2 * d ^ 2 + 2 * b1 ^ 2 * (a ^ 2 * d ^ 2) := by
    have hre : b0 * d + b1 * d + b1 * a * d =
        (b0 + b1) * d + b1 * a * d := by ring
    rw [hre]
    have hsq : ((b0 + b1) * d + b1 * a * d) ^ 2 ≤
        2 * (((b0 + b1) * d) ^ 2 + (b1 * a * d) ^ 2) :=
      add_sq_le
    rw [mul_add] at hsq
    refine hsq.trans (le_of_eq ?_)
    ring
  have e1 : 2 * (b0 + b1) ^ 2 * d ^ 2 ≤ 2 * (b0 + b1) ^ 2 * (p * u) :=
    mul_le_mul_of_nonneg_left hdu (mul_nonneg (by norm_num) (sq_nonneg _))
  have e2 : 2 * b1 ^ 2 * (a ^ 2 * d ^ 2) ≤ 2 * b1 ^ 2 * (p * u) :=
    mul_le_mul_of_nonneg_left had (mul_nonneg (by norm_num) (sq_nonneg _))
  calc
    (b0 * d + b1 * d + b1 * a * d) ^ 2 ≤
        2 * (b0 + b1) ^ 2 * d ^ 2 + 2 * b1 ^ 2 * (a ^ 2 * d ^ 2) := hstep
    _ ≤ 2 * (b0 + b1) ^ 2 * (p * u) + 2 * b1 ^ 2 * (p * u) :=
      add_le_add e1 e2
    _ = (2 * (b0 + b1) ^ 2 + 2 * b1 ^ 2) * (p * u) := by ring

theorem sq_le_one_add_pow_four {a : ℝ} (ha : 0 ≤ a) :
    a ^ 2 ≤ (1 + a) ^ 4 := by
  have h1 : a ^ 2 ≤ (1 + a) ^ 2 := pow_le_pow_left₀ ha (by linarith) 2
  have h2 : (1 : ℝ) ≤ (1 + a) ^ 2 := by nlinarith
  calc
    a ^ 2 ≤ (1 + a) ^ 2 := h1
    _ = 1 * (1 + a) ^ 2 := (one_mul _).symm
    _ ≤ (1 + a) ^ 2 * (1 + a) ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = (1 + a) ^ 4 := by ring

theorem pow_four_le_one_add_pow_four {a : ℝ} (ha : 0 ≤ a) :
    a ^ 4 ≤ (1 + a) ^ 4 :=
  pow_le_pow_left₀ ha (by linarith) 4

theorem one_le_one_add_pow_four {a : ℝ} (ha : 0 ≤ a) :
    (1 : ℝ) ≤ (1 + a) ^ 4 := by
  have h2 : (1 : ℝ) ≤ (1 + a) ^ 2 := by nlinarith
  calc
    (1 : ℝ) = 1 * 1 := (one_mul 1).symm
    _ ≤ (1 + a) ^ 2 * (1 + a) ^ 2 :=
      mul_le_mul h2 h2 zero_le_one (sq_nonneg _)
    _ = (1 + a) ^ 4 := by ring

theorem quadratic_product_bounds (Y Z P : ℝ) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hP : P = (1 + Y) ^ 2 * (1 + Z) ^ 2) :
    Z ≤ P ∧ Y ≤ P ∧ (1 + Y) * Z ≤ P ∧ (1 + Y) * Y ≤ P ∧
      (1 + Z) * Y ≤ P ∧ (1 + Y) * (1 + Y) * Z ≤ P ∧
      (1 + Y) * (1 + Z) * Y ≤ P ∧ (1 + Y) * (1 + Z) * Z ≤ P := by
  rw [hP]
  have m1 : (0 : ℝ) ≤ Y * Z := mul_nonneg hY hZ
  have m2 : (0 : ℝ) ≤ Y * Y := mul_nonneg hY hY
  have m3 : (0 : ℝ) ≤ Z * Z := mul_nonneg hZ hZ
  have m4 : (0 : ℝ) ≤ Y * Y * Z := mul_nonneg m2 hZ
  have m5 : (0 : ℝ) ≤ Y * Z * Z := mul_nonneg m1 hZ
  have m6 : (0 : ℝ) ≤ Y * Y * Z * Z := mul_nonneg m4 hZ
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem add_sq_le_young (u v θ : ℝ) (hθ : 0 < θ) :
    (u + v) ^ 2 ≤ (1 + θ) * u ^ 2 + (1 + θ⁻¹) * v ^ 2 := by
  have hkey : 2 * (u * v) ≤ θ * u ^ 2 + θ⁻¹ * v ^ 2 := by
    have h0 : 0 ≤ (θ * u - v) ^ 2 := sq_nonneg _
    have hexp : θ * (θ * u ^ 2 + θ⁻¹ * v ^ 2 - 2 * (u * v)) =
        (θ * u - v) ^ 2 := by
      field_simp
      ring
    nlinarith [h0, hexp, mul_pos hθ hθ]
  nlinarith [hkey]

theorem sqrt_add_le_add_sqrt (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hkey : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x,
      Real.sqrt_nonneg y, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc
    Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
      Real.sqrt_le_sqrt hkey
    _ = Real.sqrt x + Real.sqrt y :=
      Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y))

theorem sqrt_le_mul_sqrt_add_sqrt_of_le
    {e b K w T : ℝ} (he : 0 ≤ e) (hb : 0 ≤ b) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hT : T ≤ e ^ 2 * b + K * w) :
    Real.sqrt T ≤ e * Real.sqrt b + Real.sqrt (K * w) := by
  refine (Real.sqrt_le_sqrt hT).trans ?_
  refine (sqrt_add_le_add_sqrt (e ^ 2 * b) (K * w) (by positivity) (by positivity)).trans ?_
  rw [Real.sqrt_mul (by positivity) b, Real.sqrt_sq he]

theorem sq_sum_five_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin 5)))
    (f := ![a, b, c, d, e])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem five_term_young_bound
    {T e1 e2 b K1 K2 K3 K4 K5 w : ℝ}
    (hb : 0 ≤ b) (hw : 0 ≤ w)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hK4 : 0 ≤ K4)
    (hK5 : 0 ≤ K5) (hT0 : 0 ≤ T)
    (hT : Real.sqrt T ≤ (e1 + e2) * Real.sqrt b +
      (Real.sqrt (K1 * w) + Real.sqrt (K2 * w) + Real.sqrt (K3 * w) +
        Real.sqrt (K4 * w) + Real.sqrt (K5 * w))) :
    T ≤ ((201 / 200) * (e1 + e2)) ^ 2 * b +
      (505 * (K1 + K2 + K3 + K4 + K5)) * w := by
  set u : ℝ := (e1 + e2) * Real.sqrt b with hu_def
  set v : ℝ := Real.sqrt (K1 * w) + Real.sqrt (K2 * w) + Real.sqrt (K3 * w) +
    Real.sqrt (K4 * w) + Real.sqrt (K5 * w) with hv_def
  have hTuv : T ≤ (u + v) ^ 2 := by
    have hsq : Real.sqrt T ^ 2 ≤ (u + v) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg T) (by simpa only [hu_def, hv_def] using hT) 2
    rwa [Real.sq_sqrt hT0] at hsq
  have hyoung := add_sq_le_young u v (1 / 100) (by norm_num)
  have hu2 : u ^ 2 = (e1 + e2) ^ 2 * b := by
    rw [hu_def, mul_pow, Real.sq_sqrt hb]
  have hv2 : v ^ 2 ≤ 5 * (K1 * w + K2 * w + K3 * w + K4 * w + K5 * w) := by
    have h1 : Real.sqrt (K1 * w) ^ 2 = K1 * w := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (K2 * w) ^ 2 = K2 * w := Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt (K3 * w) ^ 2 = K3 * w := Real.sq_sqrt (by positivity)
    have h4 : Real.sqrt (K4 * w) ^ 2 = K4 * w := Real.sq_sqrt (by positivity)
    have h5 : Real.sqrt (K5 * w) ^ 2 = K5 * w := Real.sq_sqrt (by positivity)
    have hfive := sq_sum_five_le (Real.sqrt (K1 * w)) (Real.sqrt (K2 * w))
      (Real.sqrt (K3 * w)) (Real.sqrt (K4 * w)) (Real.sqrt (K5 * w))
    rw [h1, h2, h3, h4, h5] at hfive
    simpa only [hv_def] using hfive
  have hone : (1 + (1 / 100 : ℝ)) * u ^ 2 ≤
      ((201 / 200) * (e1 + e2)) ^ 2 * b := by
    rw [hu2]
    have hcoeff : (1 + (1 / 100 : ℝ)) ≤ (201 / 200 : ℝ) ^ 2 := by norm_num
    calc
      (1 + (1 / 100 : ℝ)) * ((e1 + e2) ^ 2 * b) ≤
          (201 / 200 : ℝ) ^ 2 * ((e1 + e2) ^ 2 * b) :=
        mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (sq_nonneg _) hb)
      _ = ((201 / 200) * (e1 + e2)) ^ 2 * b := by ring
  have hinv : ((1 : ℝ) / 100)⁻¹ = 100 := by norm_num
  rw [hinv] at hyoung
  calc
    T ≤ (u + v) ^ 2 := hTuv
    _ ≤ (1 + 1 / 100) * u ^ 2 + (1 + 100) * v ^ 2 := hyoung
    _ ≤ ((201 / 200) * (e1 + e2)) ^ 2 * b +
        (1 + 100) * (5 * (K1 * w + K2 * w + K3 * w + K4 * w + K5 * w)) := by
      exact add_le_add hone (mul_le_mul_of_nonneg_left hv2 (by norm_num))
    _ = ((201 / 200) * (e1 + e2)) ^ 2 * b +
        (505 * (K1 + K2 + K3 + K4 + K5)) * w := by ring

theorem sqrt_pair_add_le (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt ((a + b) ^ 2 + (c + d) ^ 2) ≤
      Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2) := by
  have hcs : a * b + c * d ≤
      Real.sqrt (a ^ 2 + c ^ 2) * Real.sqrt (b ^ 2 + d ^ 2) := by
    have h1 : (a * b + c * d) ^ 2 ≤ (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := by
      nlinarith [sq_nonneg (a * d - b * c)]
    have h2 : 0 ≤ a * b + c * d := by positivity
    have h3 : Real.sqrt ((a * b + c * d) ^ 2) ≤
        Real.sqrt ((a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2)) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq h2, Real.sqrt_mul (by positivity)] at h3
    exact h3
  have hrhs : 0 ≤ Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2) := by
    positivity
  have hexp : (a + b) ^ 2 + (c + d) ^ 2 ≤
      (Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2)) ^ 2 := by
    have e1 : Real.sqrt (a ^ 2 + c ^ 2) ^ 2 = a ^ 2 + c ^ 2 :=
      Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (b ^ 2 + d ^ 2) ^ 2 = b ^ 2 + d ^ 2 :=
      Real.sq_sqrt (by positivity)
    nlinarith [hcs]
  calc
    Real.sqrt ((a + b) ^ 2 + (c + d) ^ 2) ≤
        Real.sqrt ((Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2)) ^ 2) :=
      Real.sqrt_le_sqrt hexp
    _ = Real.sqrt (a ^ 2 + c ^ 2) + Real.sqrt (b ^ 2 + d ^ 2) :=
      Real.sqrt_sq hrhs

theorem sqrt_sq_add_sq_mono {x' x y' y : ℝ}
    (hx' : 0 ≤ x') (hy' : 0 ≤ y') (hx : x' ≤ x) (hy : y' ≤ y) :
    Real.sqrt (x' ^ 2 + y' ^ 2) ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
  refine Real.sqrt_le_sqrt ?_
  have h1 : x' ^ 2 ≤ x ^ 2 := by nlinarith
  have h2 : y' ^ 2 ≤ y ^ 2 := by nlinarith
  linarith

theorem sqrt_two_step_endpoint
    (u₂ u₃ a₁ a₂ a₃ q₁ q₂ : ℝ)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (ha₁₂ : a₁ ≤ a₂) (ha₂₃ : a₂ ≤ a₃)
    (hu₂ : u₂ ^ 2 ≤ a₂ ^ 2 + q₁ * a₁ ^ 2)
    (hu₃ : u₃ ^ 2 ≤ a₃ ^ 2 + q₂ * a₂ ^ 2) :
    Real.sqrt (u₂ ^ 2 + u₃ ^ 2) ≤
      a₃ + Real.sqrt (1 + q₁ + q₂) * a₂ := by
  have hq : 0 ≤ 1 + q₁ + q₂ := add_nonneg (add_nonneg zero_le_one hq₁) hq₂
  have hq_sq : Real.sqrt (1 + q₁ + q₂) ^ 2 = 1 + q₁ + q₂ := Real.sq_sqrt hq
  have ha₁_sq : a₁ ^ 2 ≤ a₂ ^ 2 := pow_le_pow_left₀ ha₁ ha₁₂ 2
  have ha₂_sq : a₂ ^ 2 ≤ a₃ ^ 2 := pow_le_pow_left₀ ha₂ ha₂₃ 2
  have hcross : 0 ≤ 2 * a₃ * (Real.sqrt (1 + q₁ + q₂) * a₂) :=
    mul_nonneg (mul_nonneg (by positivity) ha₃)
      (mul_nonneg (Real.sqrt_nonneg _) ha₂)
  have hsum : u₂ ^ 2 + u₃ ^ 2 ≤
      (a₃ + Real.sqrt (1 + q₁ + q₂) * a₂) ^ 2 := by
    nlinarith
  calc
    Real.sqrt (u₂ ^ 2 + u₃ ^ 2) ≤
        Real.sqrt ((a₃ + Real.sqrt (1 + q₁ + q₂) * a₂) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = a₃ + Real.sqrt (1 + q₁ + q₂) * a₂ :=
      Real.sqrt_sq (add_nonneg ha₃ (mul_nonneg (Real.sqrt_nonneg _) ha₂))

theorem sum_sq_le_sq_sum_of_nonneg
    {n : ℕ} (u : ℕ → ℝ) (hu : ∀ i, 0 ≤ u i) :
    ∑ i ∈ Finset.range n, u i ^ 2 ≤ (∑ i ∈ Finset.range n, u i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hsum : 0 ≤ ∑ i ∈ Finset.range n, u i :=
        Finset.sum_nonneg fun i _ => hu i
      nlinarith [ih, hu n, sq_nonneg (u n)]

end DifferentialGeometry.Analysis
