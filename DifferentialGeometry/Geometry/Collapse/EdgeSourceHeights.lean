import DifferentialGeometry.Geometry.Collapse.EdgeModelDirectionTransfer

/-!
# (LFR28.2): source heights converge to the model radial function (modulo LFR14 data)

Blueprint LFR28 step 1 (master207A:27286–27305). The coarse-border charts `Q i = (u_i, b_i)` centred
at `j i q` have distance distortion `τΔ` on `B(j i q, 200Δ)` and nonnegative heights; the model is a
metric product `Φ : N ≃ᵢ ℓ²(ℝ × W)` with `Φ q = (0, z₀)` and `r(x) = d_W((Φ x).2, z₀)`; the maps
`j i` have LFR14's pointed distance distortion and `u_i ∘ j_i → t` uniformly on `B̄(q, 100Δ)`.
Comparing `d(q, x)² = t² + r²` with `|Q_i(j_i x)|² = u_i² + b_i²`:

* `sq_sub_le_of_norm_sq_bounds`: the numerical step (`|a - b|² ≤ |a² - b²|` for `a, b ≥ 0`);
* `eventually_abs_height_sub_axisDist_le` (**LFR28.2**): for every `h' > 20 √τ`, eventually
  `|b_i(j_i x) - r(x)| ≤ h' Δ` on `B(q, 100Δ)`. This is exactly LFR26's height hypothesis (LFR26.1)
  with `h = 20 √τ` (the blueprint uses `40 √τ`).

Only metric data enter: no manifold structure is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

/-- Numerical step of (LFR28.2): from `|q - D| ≤ τΔ + η`, `q² = u² + b²`, `D² = t² + r²`,
`|u - t| ≤ η`, `|t| ≤ D ≤ 100Δ`, `η ≤ Δ`, `τ ≤ 1` and `b, r ≥ 0`:
`(b - r)² ≤ 202 τ Δ² + 403 Δ η`. -/
theorem sq_sub_le_of_norm_sq_bounds {q D u t b r τ Δ η : ℝ} (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (hτ1 : τ ≤ 1) (hη : 0 ≤ η) (hηΔ : η ≤ Δ) (hq0 : 0 ≤ q) (hD : D ≤ 100 * Δ)
    (hqD : |q - D| ≤ τ * Δ + η) (hqsq : q ^ 2 = u ^ 2 + b ^ 2) (hDsq : D ^ 2 = t ^ 2 + r ^ 2)
    (hu : |u - t| ≤ η) (ht : |t| ≤ D) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    (b - r) ^ 2 ≤ 202 * τ * Δ ^ 2 + 403 * Δ * η := by
  have hD0 : 0 ≤ D := (abs_nonneg t).trans ht
  have hqD' := abs_le.mp hqD
  have hu' := abs_le.mp hu
  have ht' := abs_le.mp ht
  have hτΔ : τ * Δ ≤ Δ := by nlinarith
  -- `|q² - D²| ≤ (τΔ + η) · 202Δ`
  have h1 : |q ^ 2 - D ^ 2| ≤ (τ * Δ + η) * (202 * Δ) := by
    rw [show q ^ 2 - D ^ 2 = (q - D) * (q + D) by ring, abs_mul]
    have hqD2 : |q + D| ≤ 202 * Δ := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact mul_le_mul hqD hqD2 (abs_nonneg _) (by positivity)
  -- `|u² - t²| ≤ η · 201Δ`
  have h2 : |u ^ 2 - t ^ 2| ≤ η * (201 * Δ) := by
    rw [show u ^ 2 - t ^ 2 = (u - t) * (u + t) by ring, abs_mul]
    have hut : |u + t| ≤ 201 * Δ := by
      rw [abs_le]
      constructor <;> linarith
    exact mul_le_mul hu hut (abs_nonneg _) hη
  have h3 : |b ^ 2 - r ^ 2| ≤ 202 * τ * Δ ^ 2 + 403 * Δ * η := by
    have he : b ^ 2 - r ^ 2 = (q ^ 2 - D ^ 2) - (u ^ 2 - t ^ 2) := by rw [hqsq, hDsq]; ring
    rw [he]
    calc |(q ^ 2 - D ^ 2) - (u ^ 2 - t ^ 2)| ≤ |q ^ 2 - D ^ 2| + |u ^ 2 - t ^ 2| := abs_sub _ _
      _ ≤ (τ * Δ + η) * (202 * Δ) + η * (201 * Δ) := add_le_add h1 h2
      _ = 202 * τ * Δ ^ 2 + 403 * Δ * η := by ring
  have h4 : (b - r) ^ 2 ≤ |b ^ 2 - r ^ 2| := by
    rw [show b ^ 2 - r ^ 2 = (b - r) * (b + r) by ring, abs_mul, abs_of_nonneg (by linarith : 0 ≤ b + r),
      ← sq_abs (b - r), sq]
    exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> linarith) (abs_nonneg _)
  linarith

/-- **(LFR28.2): source heights converge to the model radial function.** Pointed distance distortion
of `j i` tending to zero on balls around `q`, coarse-border charts `Q i` centred at `j i q` with
distortion `τΔ` on `B(j i q, 200Δ)` (`0 ≤ τ ≤ 1`) and nonnegative heights, a metric product
`Φ : N ≃ᵢ ℓ²(ℝ × W)` with `Φ q = (0, z₀)`, and `u_i ∘ j_i → t` uniformly on `B̄(q, 100Δ)`: for every
`h' > 20 √τ`, eventually `|b_i(j_i x) - r(x)| ≤ h' Δ` for all `x ∈ B(q, 100Δ)`. -/
theorem eventually_abs_height_sub_axisDist_le {N : Type*} [MetricSpace N] {M : ℕ → Type*}
    [∀ i, MetricSpace (M i)] (j : ∀ i, N → M i) (q : N)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {z₀ : W}
    (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀))
    {Δ τ : ℝ} (hΔ : 0 < Δ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hcoord : TendstoUniformlyOn (fun i x => (Q i (j i x)).fst) (fun x => (Φ x).fst) atTop
      (closedBall q (100 * Δ))) :
    ∀ h' : ℝ, 20 * Real.sqrt τ < h' → ∀ᶠ i in atTop, ∀ x ∈ ball q (100 * Δ),
      |(Q i (j i x)).snd - dist (Φ x).snd z₀| ≤ h' * Δ := by
  intro h' hh'
  have hsq0 : 0 ≤ 20 * Real.sqrt τ * Δ := by positivity
  have h1 : 20 * Real.sqrt τ * Δ < h' * Δ := mul_lt_mul_of_pos_right hh' hΔ
  have h2 : (20 * Real.sqrt τ * Δ) ^ 2 = 400 * τ * Δ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hτ]
    ring
  have h3 := pow_lt_pow_left₀ h1 hsq0 two_ne_zero
  have hslack : 0 < (h' * Δ) ^ 2 - 202 * τ * Δ ^ 2 := by nlinarith
  set η : ℝ := min Δ (((h' * Δ) ^ 2 - 202 * τ * Δ ^ 2) / (403 * Δ)) with hηdef
  have hη0 : 0 < η := lt_min hΔ (by positivity)
  have hηΔ : η ≤ Δ := min_le_left _ _
  have hηs : 403 * Δ * η ≤ (h' * Δ) ^ 2 - 202 * τ * Δ ^ 2 := by
    have h4 : η ≤ ((h' * Δ) ^ 2 - 202 * τ * Δ ^ 2) / (403 * Δ) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h4
    linarith
  have hq100 : q ∈ ball q (100 * Δ) := mem_ball_self (by positivity)
  filter_upwards [hdist (100 * Δ) η hη0, Metric.tendstoUniformlyOn_iff.mp hcoord η hη0]
    with i hi hci
  intro x hx
  have hxq : dist x q < 100 * Δ := hx
  have hDi := abs_lt.mp (hi x hx q hq100)
  have hjx : j i x ∈ ball (j i q) (200 * Δ) := by
    rw [mem_ball]
    linarith
  have hjq : j i q ∈ ball (j i q) (200 * Δ) := mem_ball_self (by positivity)
  have hQn := hQdist i (j i x) hjx (j i q) hjq
  rw [hQp i, dist_zero_right] at hQn
  have hqD : |‖Q i (j i x)‖ - dist x q| ≤ τ * Δ + η := by
    rw [abs_le] at hQn ⊢
    constructor <;> linarith
  have hqsq : ‖Q i (j i x)‖ ^ 2 = (Q i (j i x)).fst ^ 2 + (Q i (j i x)).snd ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have hDsq : dist x q ^ 2 = (Φ x).fst ^ 2 + dist (Φ x).snd z₀ ^ 2 := by
    rw [← Φ.dist_eq, hΦq, DifferentialGeometry.Geometry.Collapse.dist_withLp_two_prod,
      Real.sq_sqrt (by positivity)]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sub_zero, sq_abs]
  have hu : |(Q i (j i x)).fst - (Φ x).fst| ≤ η := by
    have h5 := hci x (ball_subset_closedBall hx)
    rw [Real.dist_eq, abs_sub_comm] at h5
    exact h5.le
  have ht : |(Φ x).fst| ≤ dist x q := by
    have h6 := dist_fst_le_of_withLp (Φ x) (Φ q)
    rw [Φ.dist_eq, hΦq] at h6
    simpa only [WithLp.toLp_fst, Real.dist_eq, sub_zero] using h6
  have hbound := sq_sub_le_of_norm_sq_bounds hΔ hτ hτ1 hη0.le hηΔ (norm_nonneg _) hxq.le hqD hqsq
    hDsq hu ht (hheight i _ hjx) dist_nonneg
  have h7 : ((Q i (j i x)).snd - dist (Φ x).snd z₀) ^ 2 ≤ (h' * Δ) ^ 2 := by linarith
  have h8 : 0 ≤ h' * Δ := by linarith
  calc |(Q i (j i x)).snd - dist (Φ x).snd z₀|
      = Real.sqrt (((Q i (j i x)).snd - dist (Φ x).snd z₀) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((h' * Δ) ^ 2) := Real.sqrt_le_sqrt h7
    _ = h' * Δ := Real.sqrt_sq h8

end DifferentialGeometry.Geometry.Riemannian.Geodesic
