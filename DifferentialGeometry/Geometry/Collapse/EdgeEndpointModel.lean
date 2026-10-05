import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalSegment
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# LFR28 I7(a): the step-1 endpoint model on the surface factor

Blueprint 207A, LFR28 (`thm:collapse-finite-source-edge-packet`, A:27223), proof step 1, second
paragraph ("Here is also an actual endpoint approximation ... After scaling distances by `Δ⁻¹` it
meets LFR23 with error `20τ`"). Item I7 of build-logs/worker-F7-LFR28B.md.

Model `N ≃ᵢ ℓ²(ℝ × W)` with `q ↦ (0, z₀)`, comparison maps `j_i : N → M_i` with distortion `→ 0` on
balls and source coverage, coarse-border charts `Q_i` at `j_i q` (distortion `τΔ`, nonnegative
heights, image `τΔ`-dense in the rectangle) whose first coordinate converges to `t` along `j_i`.
The height of the slice point `(0, w)` read in the source,
`edgeEndpointHeight (Q i) (j i) Φ w = b_i(j_i(0, w))`, is on every late index an endpoint model of
`B̄_W(z₀, 10Δ)` (`eventually_edgeEndpointModel`):
`z₀ ↦ 0`, nonnegative, distortion `≤ 2τΔ`, and `13τΔ`-dense in `[0, 10Δ]`.
`exists_edgeEndpointModel` fixes one such index: a single map `q : W → ℝ` with LFR23's endpoint
hypotheses at error `20τΔ` (physical units) and, after dividing values and distances by `Δ`, at
error `20τ` (the unit form LFR24 consumes).

Deviation from the blueprint: instead of limits of heights at a finite net (which needs a further
subsequence) the heights of ONE late index are used; all estimates hold on the common tail, so the
conclusion (an actual endpoint map of error `20τ`) is the same, and no limit of discontinuous maps
is taken.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric

namespace DifferentialGeometry.Geometry.Collapse

section PlaneDistance

/-- In the `ℓ²` plane, the distance and the height difference differ by at most the first-coordinate
difference. -/
theorem abs_dist_sub_abs_snd_le (a b : WithLp 2 (ℝ × ℝ)) :
    |dist a b - abs (a.snd - b.snd)| ≤ |a.fst - b.fst| := by
  rw [WithLp.prod_dist_eq_of_L2, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  set u := a.fst - b.fst
  set v := a.snd - b.snd
  have h1 : |v| ≤ Real.sqrt (u ^ 2 + v ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg u])
  have h2 : Real.sqrt (u ^ 2 + v ^ 2) ≤ |u| + |v| := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg u, abs_nonneg v, sq_abs u, sq_abs v, abs_mul_abs_self u,
      abs_mul_abs_self v]
  rw [abs_le]
  constructor <;> linarith [abs_nonneg u]

/-- The first-coordinate difference is at most the `ℓ²` distance. -/
theorem abs_fst_sub_le_dist (a b : WithLp 2 (ℝ × ℝ)) : |a.fst - b.fst| ≤ dist a b := by
  rw [WithLp.prod_dist_eq_of_L2, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (a.snd - b.snd)])

/-- The height difference is at most the `ℓ²` distance. -/
theorem abs_snd_sub_le_dist (a b : WithLp 2 (ℝ × ℝ)) : |a.snd - b.snd| ≤ dist a b := by
  rw [WithLp.prod_dist_eq_of_L2, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (a.fst - b.fst)])

/-- The `ℓ²` distance is at most the sum of the coordinate differences. -/
theorem dist_le_abs_fst_add_abs_snd (a b : WithLp 2 (ℝ × ℝ)) :
    dist a b ≤ |a.fst - b.fst| + |a.snd - b.snd| := by
  have h := abs_dist_sub_abs_snd_le a b
  linarith [(abs_le.mp h).2]

/-- Distance in `ℓ²(ℝ × W)` between points with the same factor coordinate. -/
theorem dist_toLp_same_snd {W : Type*} [PseudoMetricSpace W] (t t' : ℝ) (w : W) :
    dist (WithLp.toLp 2 (t, w)) (WithLp.toLp 2 (t', w)) = |t - t'| := by
  rw [dist_withLp_two_prod]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self, Real.dist_eq]
  rw [sq_abs, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs]

/-- Distance in `ℓ²(ℝ × W)` between points of the zero slice. -/
theorem dist_toLp_zero_fst {W : Type*} [PseudoMetricSpace W] (w w' : W) :
    dist (WithLp.toLp 2 ((0 : ℝ), w)) (WithLp.toLp 2 ((0 : ℝ), w')) = dist w w' := by
  rw [dist_withLp_two_prod]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add, Real.sqrt_sq dist_nonneg]

end PlaneDistance

section Endpoint

variable {N : Type*} [MetricSpace N] {W : Type*} [MetricSpace W]

/-- The source height of the slice point `(0, w)`: `b(j(Φ⁻¹(0, w)))`. -/
def edgeEndpointHeight {S : Type*} (Q : S → WithLp 2 (ℝ × ℝ)) (j : N → S)
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) (w : W) : ℝ :=
  (Q (j (Φ.symm (WithLp.toLp 2 ((0 : ℝ), w))))).snd

/-- **LFR28 I7(a), sequence form.** On every late index the source heights of the zero slice form
an endpoint model of `B̄_W(z₀, 10Δ)`: value `0` at `z₀`, nonnegative, distortion `≤ 2τΔ`, and
`13τΔ`-dense in `[0, 10Δ]`. -/
theorem eventually_edgeEndpointModel {M : ℕ → Type*} [∀ i, MetricSpace (M i)]
    (j : ∀ i, N → M i) (q : N)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcov : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ y ∈ ball (j i q) R,
      ∃ x ∈ ball q (R + 1), dist (j i x) y < ε)
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {z₀ : W} (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀))
    {Δ τ : ℝ} (hΔ : 1 ≤ Δ) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 1000)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hdense : ∀ i, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ y ∈ ball (j i q) (200 * Δ), dist (Q i y) z ≤ τ * Δ)
    (hcoord : TendstoUniformlyOn (fun i x => (Q i (j i x)).fst)
      (fun x => (Φ x).fst) atTop (closedBall q (100 * Δ))) :
    ∀ᶠ i in atTop,
      edgeEndpointHeight (Q i) (j i) Φ z₀ = 0 ∧
      (∀ w ∈ closedBall z₀ (10 * Δ), 0 ≤ edgeEndpointHeight (Q i) (j i) Φ w) ∧
      (∀ w ∈ closedBall z₀ (10 * Δ), ∀ w' ∈ closedBall z₀ (10 * Δ),
        |dist (edgeEndpointHeight (Q i) (j i) Φ w) (edgeEndpointHeight (Q i) (j i) Φ w') -
          dist w w'| ≤ 2 * τ * Δ) ∧
      ∀ s ∈ Icc (0 : ℝ) (10 * Δ), ∃ w ∈ closedBall z₀ (10 * Δ),
        |edgeEndpointHeight (Q i) (j i) Φ w - s| ≤ 13 * τ * Δ := by
  have hΔ0 : 0 < Δ := by linarith
  have hε : 0 < τ * Δ / 8 := by positivity
  have hτΔ : τ * Δ ≤ Δ / 1000 := by nlinarith
  filter_upwards [hdist (300 * Δ) (τ * Δ / 8) hε, hcov (20 * Δ) (τ * Δ / 8) hε,
    Metric.tendstoUniformlyOn_iff.mp hcoord (τ * Δ / 8) hε] with i hdi hci hco
  -- the slice point `(0, w)`
  set xs : W → N := fun w => Φ.symm (WithLp.toLp 2 ((0 : ℝ), w)) with hxs
  have hxsd : ∀ w w', dist (xs w) (xs w') = dist w w' := fun w w' => by
    change dist (Φ.symm (WithLp.toLp 2 ((0 : ℝ), w))) (Φ.symm (WithLp.toLp 2 ((0 : ℝ), w'))) = _
    rw [Φ.symm.dist_eq, dist_toLp_zero_fst]
  have hxsq : xs z₀ = q := by
    change Φ.symm (WithLp.toLp 2 ((0 : ℝ), z₀)) = q
    rw [← hΦq, IsometryEquiv.symm_apply_apply]
  have hxsfst : ∀ w, (Φ (xs w)).fst = 0 := fun w => by
    change (Φ (Φ.symm (WithLp.toLp 2 ((0 : ℝ), w)))).fst = 0
    rw [IsometryEquiv.apply_symm_apply]
    rfl
  have hβ : ∀ w, edgeEndpointHeight (Q i) (j i) Φ w = (Q i (j i (xs w))).snd := fun _ => rfl
  have hxsdq : ∀ w, dist (xs w) q = dist w z₀ := fun w => by rw [← hxsq, hxsd]
  -- membership bookkeeping
  have hq300 : q ∈ ball q (300 * Δ) := mem_ball_self (by positivity)
  have hjball : ∀ x ∈ ball q (300 * Δ), dist x q < 100 * Δ →
      j i x ∈ ball (j i q) (200 * Δ) := by
    intro x hx hxq
    have h := (abs_lt.mp (hdi x hx q hq300)).2
    change dist (j i x) (j i q) < 200 * Δ
    linarith
  have hjq : j i q ∈ ball (j i q) (200 * Δ) := mem_ball_self (by positivity)
  -- the first coordinate is small at slice points of the window
  have hfst : ∀ x, dist x q ≤ 100 * Δ → |(Q i (j i x)).fst - (Φ x).fst| < τ * Δ / 8 := by
    intro x hx
    have h := hco x (mem_closedBall.mpr hx)
    rwa [Real.dist_eq, abs_sub_comm] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hβ, hxsq, hQp]
    rfl
  · intro w hw
    have hw' : dist w z₀ ≤ 10 * Δ := hw
    have hx300 : xs w ∈ ball q (300 * Δ) := by
      change dist (xs w) q < 300 * Δ
      rw [hxsdq]
      linarith
    exact hheight i _ (hjball _ hx300 (by rw [hxsdq]; linarith))
  · intro w hw w' hw'
    have hw1 : dist w z₀ ≤ 10 * Δ := hw
    have hw2 : dist w' z₀ ≤ 10 * Δ := hw'
    have hx1 : xs w ∈ ball q (300 * Δ) := by
      change dist (xs w) q < 300 * Δ
      rw [hxsdq]
      linarith
    have hx2 : xs w' ∈ ball q (300 * Δ) := by
      change dist (xs w') q < 300 * Δ
      rw [hxsdq]
      linarith
    have hj1 := hjball _ hx1 (by rw [hxsdq]; linarith)
    have hj2 := hjball _ hx2 (by rw [hxsdq]; linarith)
    have hQd := hQdist i _ hj1 _ hj2
    have hjd := hdi _ hx1 _ hx2
    rw [hxsd] at hjd
    have hf1 := hfst (xs w) (by rw [hxsdq]; linarith)
    have hf2 := hfst (xs w') (by rw [hxsdq]; linarith)
    rw [hxsfst, sub_zero] at hf1 hf2
    have hpl := abs_dist_sub_abs_snd_le (Q i (j i (xs w))) (Q i (j i (xs w')))
    have hfd : |(Q i (j i (xs w))).fst - (Q i (j i (xs w'))).fst| < τ * Δ / 4 := by
      have := abs_sub (Q i (j i (xs w))).fst (Q i (j i (xs w'))).fst
      linarith
    rw [hβ, hβ, Real.dist_eq]
    have e1 := abs_le.mp hpl
    have e2 := abs_le.mp hQd
    have e3 := abs_lt.mp hjd
    rw [abs_le]
    constructor <;> nlinarith
  · intro s hs
    by_cases hsmall : s ≤ 8 * τ * Δ
    · refine ⟨z₀, mem_closedBall_self (by positivity), ?_⟩
      rw [hβ, hxsq, hQp]
      change |(0 : ℝ) - s| ≤ 13 * τ * Δ
      rw [zero_sub, abs_neg, abs_of_nonneg hs.1]
      nlinarith
    push Not at hsmall
    set s' := s - 8 * τ * Δ with hs'
    have hs'0 : 0 ≤ s' := by linarith
    have hs'10 : s' ≤ 10 * Δ := by linarith [hs.2]
    obtain ⟨y, hy, hyQ⟩ := hdense i (WithLp.toLp 2 ((0 : ℝ), s'))
      (by simp only [WithLp.toLp_fst, abs_zero]; positivity)
      (by simp only [WithLp.toLp_snd]; exact ⟨hs'0, by linarith⟩)
    -- the source point is close to the chart origin
    have hyq : dist y (j i q) ≤ s' + 2 * (τ * Δ) := by
      have h1 := (abs_le.mp (hQdist i y hy (j i q) hjq)).1
      rw [hQp] at h1
      have h2 : dist (Q i y) 0 ≤ dist (Q i y) (WithLp.toLp 2 ((0 : ℝ), s')) +
          dist (WithLp.toLp 2 ((0 : ℝ), s')) 0 := dist_triangle _ _ _
      have h3 : dist (WithLp.toLp 2 ((0 : ℝ), s')) (0 : WithLp 2 (ℝ × ℝ)) = s' := by
        rw [show (0 : WithLp 2 (ℝ × ℝ)) = WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)) from rfl,
          WithLp.prod_dist_eq_of_L2]
        simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self, Real.dist_eq, sub_zero]
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add, sq_abs, Real.sqrt_sq hs'0]
      linarith
    have hy20 : y ∈ ball (j i q) (20 * Δ) := by
      change dist y (j i q) < 20 * Δ
      linarith
    obtain ⟨x, hx, hjx⟩ := hci y hy20
    have hxq : dist x q < 20 * Δ + 1 := hx
    have hx300 : x ∈ ball q (300 * Δ) := by
      change dist x q < 300 * Δ
      linarith
    have hjx200 : j i x ∈ ball (j i q) (200 * Δ) := hjball x hx300 (by linarith)
    -- the first coordinate of `x` is small
    set t := (Φ x).fst with ht
    set w := (Φ x).snd with hw
    have hQyfst : |(Q i y).fst| ≤ τ * Δ := by
      have h := abs_fst_sub_le_dist (Q i y) (WithLp.toLp 2 ((0 : ℝ), s'))
      simp only [WithLp.toLp_fst, sub_zero] at h
      linarith
    have hQysnd : |(Q i y).snd - s'| ≤ τ * Δ := by
      have h := abs_snd_sub_le_dist (Q i y) (WithLp.toLp 2 ((0 : ℝ), s'))
      simp only [WithLp.toLp_snd] at h
      linarith
    have hQxy : dist (Q i (j i x)) (Q i y) ≤ τ * Δ / 8 + τ * Δ := by
      have h := (abs_le.mp (hQdist i _ hjx200 y hy)).2
      linarith
    have ht2 : |t| ≤ 9 / 4 * (τ * Δ) := by
      have h1 := hfst x (by linarith)
      have h2 := abs_fst_sub_le_dist (Q i (j i x)) (Q i y)
      have h3 := abs_sub_abs_le_abs_sub (Q i (j i x)).fst (Q i y).fst
      have h4 := abs_sub_abs_le_abs_sub t (Q i (j i x)).fst
      rw [abs_sub_comm] at h1
      linarith
    -- the slice point over `x`
    have hΦx : Φ x = WithLp.toLp 2 (t, w) := rfl
    have hxw : dist (xs w) x = |t| := by
      change dist (Φ.symm (WithLp.toLp 2 ((0 : ℝ), w))) x = |t|
      rw [← Φ.symm_apply_apply x, Φ.symm.dist_eq, hΦx, dist_toLp_same_snd,
        zero_sub, abs_neg]
    have hxwq : dist (xs w) q < 20 * Δ + 1 + 9 / 4 * (τ * Δ) := by
      have := dist_triangle (xs w) x q
      linarith
    have hxw300 : xs w ∈ ball q (300 * Δ) := by
      change dist (xs w) q < 300 * Δ
      linarith
    have hjxw200 : j i (xs w) ∈ ball (j i q) (200 * Δ) := hjball _ hxw300 (by linarith)
    have hjxwx : dist (j i (xs w)) (j i x) < |t| + τ * Δ / 8 := by
      have h := (abs_lt.mp (hdi _ hxw300 x hx300)).2
      rw [hxw] at h
      linarith
    have hQwy : dist (Q i (j i (xs w))) (Q i y) ≤ 7 / 2 * (τ * Δ) := by
      have h1 := (abs_le.mp (hQdist i _ hjxw200 y hy)).2
      have h2 := dist_triangle (j i (xs w)) (j i x) y
      linarith
    have hβs' : |edgeEndpointHeight (Q i) (j i) Φ w - s'| ≤ 9 / 2 * (τ * Δ) := by
      rw [hβ]
      have h1 := abs_snd_sub_le_dist (Q i (j i (xs w))) (Q i y)
      have h2 := abs_sub_le (Q i (j i (xs w))).snd (Q i y).snd s'
      linarith
    -- the slice point lies in the window
    have hwz : dist w z₀ ≤ 10 * Δ := by
      rw [← hxsdq]
      have h1 := (abs_lt.mp (hdi _ hxw300 q hq300)).1
      have h2 := (abs_le.mp (hQdist i _ hjxw200 (j i q) hjq)).1
      rw [hQp] at h2
      have h3 := dist_le_abs_fst_add_abs_snd (Q i (j i (xs w))) 0
      have h4 := hfst (xs w) (by linarith)
      rw [hxsfst, sub_zero] at h4
      have h5 : (0 : WithLp 2 (ℝ × ℝ)).fst = 0 := rfl
      have h6 : (0 : WithLp 2 (ℝ × ℝ)).snd = 0 := rfl
      rw [h5, h6, sub_zero, sub_zero] at h3
      have h7 : 0 ≤ (Q i (j i (xs w))).snd := hheight i _ hjxw200
      rw [abs_of_nonneg h7] at h3
      have h8 := (abs_le.mp hβs').2
      rw [hβ] at h8
      have h9 : s' = s - 8 * (τ * Δ) := by rw [hs']; ring
      linarith [hs.2]
    refine ⟨w, mem_closedBall.mpr hwz, ?_⟩
    have h := abs_sub_le (edgeEndpointHeight (Q i) (j i) Φ w) s' s
    have h2 : |s' - s| = 8 * τ * Δ := by
      rw [hs', show s - 8 * τ * Δ - s = -(8 * τ * Δ) by ring, abs_neg,
        abs_of_pos (by positivity)]
    linarith

/-- **LFR28 I7(a): one actual endpoint model.** There is a single map `q : W → ℝ` (the source heights
of the zero slice at one late index) with LFR23's endpoint hypotheses on `B̄_W(z₀, 10Δ)` at error
`20τΔ`, and, dividing values and distances by `Δ`, at error `20τ` on the `10`-ball of the rescaled
factor. -/
theorem exists_edgeEndpointModel {M : ℕ → Type*} [∀ i, MetricSpace (M i)]
    (j : ∀ i, N → M i) (q : N)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcov : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ y ∈ ball (j i q) R,
      ∃ x ∈ ball q (R + 1), dist (j i x) y < ε)
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {z₀ : W} (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀))
    {Δ τ : ℝ} (hΔ : 1 ≤ Δ) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 1000)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hdense : ∀ i, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ y ∈ ball (j i q) (200 * Δ), dist (Q i y) z ≤ τ * Δ)
    (hcoord : TendstoUniformlyOn (fun i x => (Q i (j i x)).fst)
      (fun x => (Φ x).fst) atTop (closedBall q (100 * Δ))) :
    ∃ e : W → ℝ, e z₀ = 0 ∧
      (∀ w ∈ closedBall z₀ (10 * Δ), 0 ≤ e w) ∧
      (∀ w ∈ closedBall z₀ (10 * Δ), ∀ w' ∈ closedBall z₀ (10 * Δ),
        |dist (e w) (e w') - dist w w'| ≤ 20 * τ * Δ) ∧
      (∀ s ∈ Icc (0 : ℝ) (10 * Δ), ∃ w ∈ closedBall z₀ (10 * Δ), |e w - s| ≤ 20 * τ * Δ) ∧
      (∀ w, dist w z₀ / Δ ≤ 10 → 0 ≤ e w / Δ) ∧
      (∀ w w', dist w z₀ / Δ ≤ 10 → dist w' z₀ / Δ ≤ 10 →
        |dist (e w / Δ) (e w' / Δ) - dist w w' / Δ| ≤ 20 * τ) ∧
      ∀ s ∈ Icc (0 : ℝ) 10, ∃ w, dist w z₀ / Δ ≤ 10 ∧ |e w / Δ - s| ≤ 20 * τ := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨i, h0, hnn, hdis, hden⟩ := (eventually_edgeEndpointModel j q hdist hcov Φ hΦq hΔ hτ
    hτ1 Q hQp hQdist hheight hdense hcoord).exists
  set e := edgeEndpointHeight (Q i) (j i) Φ
  have hball : ∀ w, dist w z₀ / Δ ≤ 10 ↔ w ∈ closedBall z₀ (10 * Δ) := fun w => by
    rw [mem_closedBall, div_le_iff₀ hΔ0, mul_comm]
  have hdis20 : ∀ w ∈ closedBall z₀ (10 * Δ), ∀ w' ∈ closedBall z₀ (10 * Δ),
      |dist (e w) (e w') - dist w w'| ≤ 20 * τ * Δ := fun w hw w' hw' =>
    (hdis w hw w' hw').trans (by nlinarith)
  have hden20 : ∀ s ∈ Icc (0 : ℝ) (10 * Δ), ∃ w ∈ closedBall z₀ (10 * Δ),
      |e w - s| ≤ 20 * τ * Δ := fun s hs => by
    obtain ⟨w, hw, hws⟩ := hden s hs
    exact ⟨w, hw, hws.trans (by nlinarith)⟩
  refine ⟨e, h0, hnn, hdis20, hden20, fun w hw => div_nonneg (hnn w ((hball w).mp hw)) hΔ0.le,
    fun w w' hw hw' => ?_, fun s hs => ?_⟩
  · have h := hdis20 w ((hball w).mp hw) w' ((hball w').mp hw')
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hΔ0, ← sub_div, abs_div,
      abs_of_pos hΔ0, div_le_iff₀ hΔ0]
    rwa [Real.dist_eq] at h
  · obtain ⟨w, hw, hws⟩ := hden20 (Δ * s) ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
    refine ⟨w, (hball w).mpr hw, ?_⟩
    rw [show e w / Δ - s = (e w - Δ * s) / Δ by field_simp, abs_div, abs_of_pos hΔ0,
      div_le_iff₀ hΔ0]
    linarith

end Endpoint

end DifferentialGeometry.Geometry.Collapse
