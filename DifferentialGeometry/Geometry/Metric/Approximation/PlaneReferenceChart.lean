import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.CoarseBorderDistance
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

/-!
# LFR35, metric part: the plane comparison map of a coarse-border chart and its anchors

Blueprint 207A, LFR35 (`lem:collapse-edge-plane-reference`, A:27944–28071), first paragraph of the
proof. For a coarse-border chart `Q = (u, b)` (LFR25.1, taken unbundled as in
`CoarseBorderDistance.lean`), a point `x ∈ B(p, 15Δ)` at height `b(x) ∈ [.08Δ, 10.2Δ]` and a scale
`q ∈ [.99, 1.01]`, the ACTUAL map
`Φ_x(y) = (Q(y) - Q(x)) / q` on `B(p, 200Δ)`, extended by zero,
is a pointed KL `β₂`-approximation from `(X, d/q, x)` to the Euclidean plane (a two-splitting with
singleton residual factor), once `Δ > 10⁵/β₂` and `4τΔ < β₂`. The four anchor targets
`Q(x) ± (Δ/40) e_j` (more generally every `Q(x) + v`, `‖v‖ ≤ Δ/40`) have actual lifts in `B(p, 20Δ)`
with `Q`-error at most `τΔ`.

`exists_planeComparison_kleinerLott_of_infDist` derives the height window from the row's
hypothesis `.09Δ ≤ d_A(x) ≤ 10.1Δ` through LFR25.2 (`coarseBorder_abs_infDist_sub_height_le`, lane
W4-F7d1). Only the distortion, the rectangle coverage and `Q p = 0` enter the kernel; no curvature,
completeness or continuity is used. The smooth reference coordinates `χ_x` (items 1–3 of the row) are
not part of this file.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [mX : MetricSpace X]

/-- The plane comparison map of LFR35.2: `(Q y - Q x)/q` on `B(p, 200Δ)`, zero elsewhere. -/
noncomputable def planeComparisonMap (Q : X → WithLp 2 (ℝ × ℝ)) (p x : X) (Δ q : ℝ) :
    X → WithLp 2 (ℝ × ℝ) :=
  (ball p (200 * Δ)).indicator fun y => q⁻¹ • (Q y - Q x)

section Chart

variable {Q : X → WithLp 2 (ℝ × ℝ)} {p x : X} {Δ τ β₂ q : ℝ}

theorem planeComparisonMap_of_mem {y : X} (hy : y ∈ ball p (200 * Δ)) :
    planeComparisonMap Q p x Δ q y = q⁻¹ • (Q y - Q x) :=
  indicator_of_mem hy _

theorem planeComparisonMap_of_not_mem {y : X} (hy : y ∉ ball p (200 * Δ)) :
    planeComparisonMap Q p x Δ q y = 0 :=
  indicator_of_notMem hy _

/-- Height and center bounds put every target `Q x + v`, `‖v‖ ≤ Δ/10`, inside the chart rectangle. -/
theorem planeComparison_target_mem_rectangle (hΔ : 0 < Δ) (hτ : τ ≤ 1 / 10000)
    (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (hlow : 8 / 100 * Δ ≤ (Q x).snd) (hhigh : (Q x).snd ≤ 102 / 10 * Δ)
    {v : WithLp 2 (ℝ × ℝ)} (hv : ‖v‖ ≤ Δ / 20) :
    |(Q x + v).fst| ≤ 100 * Δ ∧ (Q x + v).snd ∈ Icc 0 (100 * Δ) ∧ ‖Q x‖ < 16 * Δ := by
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hx200 : x ∈ ball p (200 * Δ) := ball_subset_ball (by linarith) hx
  have hQx : ‖Q x‖ ≤ dist x p + τ * Δ := by
    have h := (abs_le.mp (hdist x hx200 p hp)).2
    rw [hQp, dist_zero_right] at h
    linarith
  have hxp : dist x p < 15 * Δ := hx
  have hτΔ : τ * Δ ≤ Δ / 10000 := by nlinarith
  have hnx : ‖Q x‖ < 16 * Δ := by linarith
  have h1 := abs_fst_le_norm_withLp (Q x)
  have h2 := abs_fst_le_norm_withLp v
  have h3 : |v.snd| ≤ ‖v‖ := by
    have h := WithLp.prod_norm_sq_eq_of_L2 v
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg |v.fst|])
  have hfst : (Q x + v).fst = (Q x).fst + v.fst := rfl
  have hsnd : (Q x + v).snd = (Q x).snd + v.snd := rfl
  refine ⟨?_, ?_, hnx⟩
  · rw [hfst]
    exact (abs_add_le _ _).trans (by linarith)
  · rw [hsnd]
    have := abs_le.mp (h3.trans hv)
    constructor <;> linarith

/-- **LFR35, anchors.** Every target `Q(x) + v` with `‖v‖ ≤ Δ/40` (in particular the four anchors
`Q(x) ± (Δ/40) e_j`) has an actual lift `a ∈ B(p, 20Δ)` with `Q`-error at most `τΔ`. -/
theorem exists_planeComparison_anchor (hΔ : 0 < Δ) (hτ : τ ≤ 1 / 10000)
    (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (hlow : 8 / 100 * Δ ≤ (Q x).snd) (hhigh : (Q x).snd ≤ 102 / 10 * Δ)
    {v : WithLp 2 (ℝ × ℝ)} (hv : ‖v‖ ≤ Δ / 40) :
    ∃ a ∈ ball p (20 * Δ), dist (Q a) (Q x + v) ≤ τ * Δ := by
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  obtain ⟨hf, hs, hnx⟩ := planeComparison_target_mem_rectangle hΔ hτ hQp hdist hx hlow hhigh
    (hv.trans (by linarith))
  obtain ⟨a, ha, hQa⟩ := hcover _ hf hs
  refine ⟨a, ?_, hQa⟩
  have h := (abs_le.mp (hdist a ha p hp)).1
  rw [hQp, dist_zero_right] at h
  have hn : ‖Q a‖ ≤ ‖Q x‖ + ‖v‖ + τ * Δ := by
    have h1 : ‖Q a‖ ≤ ‖Q a - (Q x + v)‖ + ‖Q x + v‖ := norm_le_norm_sub_add _ _
    rw [← dist_eq_norm] at h1
    linarith [norm_add_le (Q x) v]
  have hτΔ : τ * Δ ≤ Δ / 10000 := by nlinarith
  change dist a p < 20 * Δ
  linarith

/-- **LFR35, the plane comparison map.** In the metric `d/q`, `planeComparisonMap` is a pointed KL
`β₂`-approximation to the Euclidean plane based at `x`. -/
theorem exists_planeComparison_kleinerLott (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100)
    (hβ₂Δ : 100000 / β₂ < Δ) (hτ : τ ≤ 1 / 10000) (hτβ : 4 * (τ * Δ) < β₂)
    (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (hlow : 8 / 100 * Δ ≤ (Q x).snd) (hhigh : (Q x).snd ≤ 102 / 10 * Δ)
    (hq : 99 / 100 ≤ q) (hq' : q ≤ 101 / 100) :
    letI := mX.rescale q⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq))
    ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β₂,
      ∀ y, Φ.toFun y = @planeComparisonMap X mX Q p x Δ q y := by
  have hΔpos : 0 < Δ := by linarith
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hx200 : x ∈ ball p (200 * Δ) := ball_subset_ball (by linarith) hx
  have hxp : dist x p < 15 * Δ := hx
  have hτ0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  have hβinv : β₂⁻¹ < Δ / 100000 := by
    rw [← one_div]
    have h := (div_lt_iff₀ hβ₂).mp hβ₂Δ
    rw [div_lt_div_iff₀ hβ₂ (by norm_num)]
    linarith
  have hβinv0 : 0 < β₂⁻¹ := inv_pos.mpr hβ₂
  have hqinv : q⁻¹ ≤ 100 / 99 := by
    rw [inv_le_comm₀ hq0 (by norm_num)]
    linarith
  have hqinv0 : 0 < q⁻¹ := inv_pos.mpr hq0
  -- source radius in the original metric
  have hsrc (y : X) (hy : q⁻¹ * dist y x < β₂⁻¹) : y ∈ ball p (200 * Δ) := by
    have h1 : dist y x < q * β₂⁻¹ := by
      rw [← div_eq_inv_mul, div_lt_iff₀ hq0] at hy
      linarith
    change dist y p < 200 * Δ
    have := dist_triangle y x p
    nlinarith
  have hΦ (y : X) (hy : y ∈ ball p (200 * Δ)) : planeComparisonMap Q p x Δ q y = q⁻¹ • (Q y - Q x) :=
    indicator_of_mem hy _
  have hdistΦ (y y' : X) (hy : y ∈ ball p (200 * Δ)) (hy' : y' ∈ ball p (200 * Δ)) :
      dist (planeComparisonMap Q p x Δ q y) (planeComparisonMap Q p x Δ q y') =
        q⁻¹ * dist (Q y) (Q y') := by
    rw [hΦ y hy, hΦ y' hy', dist_smul₀, Real.norm_eq_abs, abs_of_pos hqinv0, dist_sub_right]
  have hzero : (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)) : WithLp 2 (ℝ × ℝ)) = 0 := rfl
  let := mX.rescale q⁻¹ hqinv0
  have hd (y y' : X) : dist y y' = q⁻¹ * @dist X mX.toDist y y' :=
    MetricSpace.rescale_dist mX q⁻¹ hqinv0 y y'
  refine ⟨⟨hβ₂, by linarith, @planeComparisonMap X mX Q p x Δ q, ?_, ?_, ?_⟩, fun y => rfl⟩
  · rw [hΦ x hx200, sub_self, smul_zero, hzero]
  · intro y hy y' hy'
    have hy0 : y ∈ @ball X mX.toPseudoMetricSpace p (200 * Δ) := hsrc y (by rw [← hd]; exact hy)
    have hy0' : y' ∈ @ball X mX.toPseudoMetricSpace p (200 * Δ) := hsrc y' (by rw [← hd]; exact hy')
    rw [hdistΦ y y' hy0 hy0', hd, ← mul_sub, abs_mul, abs_of_pos hqinv0]
    calc q⁻¹ * |dist (Q y) (Q y') - @dist X mX.toDist y y'|
        ≤ (100 / 99) * (τ * Δ) :=
          mul_le_mul hqinv (hdist y hy0 y' hy0') (abs_nonneg _) (by norm_num)
      _ ≤ β₂ := by linarith
  · intro z hz
    rw [hzero, dist_zero_right] at hz
    have hqz : ‖q • z‖ ≤ Δ / 20 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0]
      nlinarith
    obtain ⟨hf, hs, _⟩ := planeComparison_target_mem_rectangle (mX := mX) hΔpos hτ hQp hdist hx hlow
      hhigh hqz
    obtain ⟨y, hy, hQy⟩ := hcover _ hf hs
    have himg : dist z (@planeComparisonMap X mX Q p x Δ q y) ≤ β₂ := by
      rw [hΦ y hy]
      have heq : z = q⁻¹ • ((Q x + q • z) - Q x) := by
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hq0.ne', one_smul]
      rw [heq, dist_smul₀, Real.norm_eq_abs, abs_of_pos hqinv0, dist_sub_right, dist_comm]
      calc q⁻¹ * dist (Q y) (Q x + q • z) ≤ (100 / 99) * (τ * Δ) :=
            mul_le_mul hqinv hQy dist_nonneg (by norm_num)
        _ ≤ β₂ := by linarith
    have hyx : q⁻¹ * @dist X mX.toDist y x < β₂⁻¹ := by
      have h1 := (abs_le.mp (hdist y hy x hx200)).1
      have h2 : dist (Q y) (Q x) ≤ τ * Δ + q * ‖z‖ := by
        have := dist_triangle (Q y) (Q x + q • z) (Q x)
        rw [dist_eq_norm (Q x + q • z) (Q x), add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hq0] at this
        linarith
      have h3 : @dist X mX.toDist y x ≤ q * ‖z‖ + 2 * (τ * Δ) := by linarith
      calc q⁻¹ * @dist X mX.toDist y x ≤ q⁻¹ * (q * ‖z‖ + 2 * (τ * Δ)) :=
            mul_le_mul_of_nonneg_left h3 hqinv0.le
        _ = ‖z‖ + q⁻¹ * (2 * (τ * Δ)) := by
            rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hq0.ne', one_mul]
        _ ≤ ‖z‖ + (100 / 99) * (2 * (τ * Δ)) := by
            have := mul_le_mul_of_nonneg_right hqinv (by positivity : (0 : ℝ) ≤ 2 * (τ * Δ))
            linarith
        _ < β₂⁻¹ := by linarith
    have hymem : y ∈ ball x β₂⁻¹ := by
      change dist y x < β₂⁻¹
      rw [hd]
      exact hyx
    exact (infDist_le_dist_of_mem (mem_image_of_mem _ hymem)).trans himg

/-- **LFR35, metric part, with the row's hypotheses.** For a coarse-border chart (LFR25.1 clauses),
`x ∈ B(p, 15Δ)` with `.09Δ ≤ d_A(x) ≤ 10.1Δ` and `q ∈ [.99, 1.01]`: the plane comparison map is a pointed
KL `β₂`-approximation in `d/q`, and every anchor target `Q(x) + v`, `‖v‖ ≤ Δ/40`, has an actual lift
in `B(p, 20Δ)` with `Q`-error at most `τΔ`. The height window comes from LFR25.2. -/
theorem exists_planeComparison_of_infDist {A : Set X} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂small : β₂ < 1 / 100) (hβ₂Δ : 100000 / β₂ < Δ) (hτ : τ ≤ 1 / 10000)
    (hτβ : 4 * (τ * Δ) < β₂)
    (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (hxA : 9 / 100 * Δ ≤ infDist x A) (hxA' : infDist x A ≤ 101 / 10 * Δ)
    (hq : 99 / 100 ≤ q) (hq' : q ≤ 101 / 100) :
    (letI := mX.rescale q⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq));
      ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β₂,
        ∀ y, Φ.toFun y = @planeComparisonMap X mX Q p x Δ q y) ∧
      ∀ v : WithLp 2 (ℝ × ℝ), ‖v‖ ≤ Δ / 40 →
        ∃ a ∈ ball p (20 * Δ), dist (Q a) (Q x + v) ≤ τ * Δ := by
  have hΔpos : 0 < Δ := by linarith
  have hb := coarseBorder_abs_infDist_sub_height_le hΔpos (hτ.trans (by norm_num)) hQp hdist hheight
    hpA hborder hbordercover (ball_subset_ball (by linarith) hx)
  have hτΔ : τ * Δ ≤ Δ / 10000 := by nlinarith
  have hlow : 8 / 100 * Δ ≤ (Q x).snd := by linarith [(abs_le.mp hb).2]
  have hhigh : (Q x).snd ≤ 102 / 10 * Δ := by linarith [(abs_le.mp hb).1]
  exact ⟨exists_planeComparison_kleinerLott hΔ hβ₂ hβ₂small hβ₂Δ hτ hτβ hQp hdist hcover hx hlow
    hhigh hq hq', fun v hv => exists_planeComparison_anchor hΔpos hτ hQp hdist hcover hx hlow hhigh hv⟩

end Chart

end GC.MetricGeometry
