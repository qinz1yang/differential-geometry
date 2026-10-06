import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeChartTests
import DifferentialGeometry.Geometry.Fibration.ActualEdgeConstantComparison

/-!
# A4 / G11 (lane S-BASES-PORT), group G1c (part 1): the derivative lower bound of the edge chart

The edge chart (`EdgeChart`, LC84) has no `derivative` clause (the slim chart has LFR20.1).
This file derives it from `EdgeChart.test` and the split coverage, as the circle Gram lemma
`circleAdapted_gram_lower_BBP` does for the circle chart:

* `EdgeFamilyOn.lift_BBP`: the raw-axis lift of `x` by `t ≥ 0` (family form of the undelivered
  `edge_lift_KA4_BAUGP`, from the delivered `exists_edge_split_KC2_BAUGP` and the generic
  `kl_lift_KA4`);
* **`EdgeFamilyOn.unit_lower_BBP`**: at every `x ∈ B(j, 100Δρ(j))` there is a unit vector `v` of
  `ρ(j)⁻²g` with `1 − (σ_c + b) ≤ dη_j(v)` (long test toward the lift at distance `≈ 200Δρ(j)`,
  Hopf–Rinow direction `exists_minimizing_direction_KC2_BAUGP`, scalar step
  `long_test_scalar_KA4`). Register premises: `1 ≤ Δ`, `0 < b ≤ 1/(1000Δ)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section EdgeLowerBBP

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ} {U₁ U₂ : Set X}

/-- The edge chart's own raw-axis lift (family form of `edge_lift_KA4_BAUGP`): for
`d(x, j) < R_x ρ(j)` and `t ≥ 0` with `R_x + t + 2b ≤ b⁻¹`, some `y` has
`|ρ(j)⁻¹ d(x, y) − t| ≤ 3b`, `|u_j(y) − u_j(x) − t| < 2b` and `ρ(j)⁻¹ d(y, j) < R_x + t + 4b`. -/
theorem EdgeFamilyOn.lift_BBP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂)
    {j : X} (hj : j ∈ F.centres) {x : X} {Rx t : ℝ} (hx : dist x j < Rx * ρ j)
    (ht : 0 ≤ t) (hroom : Rx + t + 2 * b ≤ b⁻¹) :
    ∃ y, |(ρ j)⁻¹ * dist x y - t| ≤ 3 * b ∧
      |egpRaw_BAUGP F j y - egpRaw_BAUGP F j x - t| < 2 * b ∧
        (ρ j)⁻¹ * dist y j < Rx + t + 4 * b := by
  have hrj := hρ j
  obtain ⟨Y, mY, q, f, hf⟩ := exists_edge_split_KC2_BAUGP F hj
  obtain ⟨f', hf'⟩ := exists_finOne_split_KA3 f
  have hxR : @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)).toDist x j < Rx := by
    rw [MetricSpace.rescale_dist, inv_mul_lt_iff₀ hrj]
    linarith
  have hξ : ‖(EuclideanSpace.single 0 1 : ℝ¹)‖ = 1 := by simp
  obtain ⟨y, -, h1, h2, h3⟩ := @kl_lift_KA4 X Y (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) mY 1 j q b
    f' x Rx t hxR _ hξ ht hroom
  rw [MetricSpace.rescale_dist] at h1 h3
  refine ⟨y, h1, ?_, h3⟩
  rw [hf' y, hf' x, hf y, hf x] at h2
  have he : EuclideanSpace.single (0 : Fin 1) (egpRaw_BAUGP F j y) -
      EuclideanSpace.single 0 (egpRaw_BAUGP F j x) - t • EuclideanSpace.single 0 (1 : ℝ) =
      EuclideanSpace.single 0 (egpRaw_BAUGP F j y - egpRaw_BAUGP F j x - t) := by
    ext k
    fin_cases k
    simp
  rw [he, PiLp.norm_single, Real.norm_eq_abs] at h2
  exact h2


/-- **The lower derivative bound of the edge coordinate** (the missing `derivative` clause of the
edge chart; edge twin of `circleAdapted_gram_lower_BBP` / LFR20.1): at every `x ∈ B(j, 100Δρ(j))`
there is a unit vector `v` of `ρ(j)⁻²g` with `1 − (σ_c + b) ≤ dη_j(v)`. The long test of
`EdgeChart.test` toward the raw-axis lift `y` of `x` at distance `≈ 200Δρ(j)`
(`EdgeFamilyOn.lift_BBP`, a Hopf–Rinow minimizing direction), and the scalar step
`long_test_scalar_KA4`. Register premises: `1 ≤ Δ`, `0 < b ≤ 1/(1000Δ)`. -/
theorem EdgeFamilyOn.unit_lower_BBP
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂)
    (hΔ : 1 ≤ Δ) (hb0 : 0 < b) (hb : b ≤ 1 / (1000 * Δ)) {j : X} (hj : j ∈ F.centres) {x : X}
    (hx : x ∈ ball j (100 * Δ * ρ j)) :
    ∃ v : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x v v = 1 ∧
      1 - (σc + b) ≤ mvfderiv 𝓘(ℝ, E3) (F.coord_BAUGA j) x v := by
  have hrj := hρ j
  have hb1 : b ≤ 1 / 1000 := by
    refine hb.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hbinv : 1000 * Δ ≤ b⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hb0]
    have : b ≤ (1000 * Δ)⁻¹ := by simpa [one_div] using hb
    exact this
  have hxj : dist x j < 100 * Δ * ρ j := mem_ball.mp hx
  obtain ⟨y, h1, h2, h3⟩ := F.lift_BBP hj (Rx := 100 * Δ) (t := 200 * Δ) hxj (by linarith)
    (by linarith)
  have hd1 : 200 * Δ - 3 * b ≤ (ρ j)⁻¹ * dist x y := by linarith [(abs_le.mp h1).1]
  have hd2 : (ρ j)⁻¹ * dist x y ≤ 200 * Δ + 3 * b := by linarith [(abs_le.mp h1).2]
  have hxy : 100 * Δ * ρ j < dist x y := by
    have h : 100 * Δ < (ρ j)⁻¹ * dist x y := by linarith
    rwa [lt_inv_mul_iff₀ hrj, mul_comm] at h
  have hyj : y ∈ ball j (1000 * Δ * ρ j) := by
    rw [mem_ball]
    have h : (ρ j)⁻¹ * dist y j < 1000 * Δ := by linarith
    rwa [inv_mul_lt_iff₀ hrj, mul_comm] at h
  have hne : x ≠ y := fun h => by
    rw [h, dist_self] at hxy
    nlinarith [mul_pos (by linarith : (0 : ℝ) < Δ) hrj]
  obtain ⟨v, hv, hgeo⟩ := exists_minimizing_direction_KC2_BAUGP g hmetric hrj hne
  refine ⟨v, hv, ?_⟩
  have hT := F.test_at_scale_KC2_BAUGP hj hrj hx hyj hxy v hv hgeo
  rw [div_self hrj.ne', one_mul, one_mul] at hT
  have hDpos : 0 < (ρ j)⁻¹ * dist x y := by linarith
  have hq : 1 / (200 * Δ + 3 * b) ≤ ((ρ j)⁻¹ * dist x y)⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hDpos hd2
  have hT' : |mvfderiv 𝓘(ℝ, E3) (F.coord_BAUGA j) x v -
      ((ρ j)⁻¹ * dist x y)⁻¹ * (egpRaw_BAUGP F j y - egpRaw_BAUGP F j x)| < σc := by
    simpa [div_eq_inv_mul] using hT
  exact long_test_scalar_KA4 (by linarith) hb0.le hb1 hq (by linarith [(abs_lt.mp h2).1]) hT'

end EdgeLowerBBP

end DifferentialGeometry.Geometry.Collapse
