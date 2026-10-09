import DifferentialGeometry.Geometry.Fibration.ActualSlimConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualFirstComparisonList

/-!
# FC23 items 1–2 at the two-stratum base: the original overlap binding packet

Blueprint `master207B.tex`, FC23 (`found:fibration-original-binding`, B:1505–1541): for each local
model used in FC07 (the circle base `i`, `D_i = B(i, 10ρ(i))`, metric `ρ(i)⁻²g`) a FINITE collection
of constant affine comparisons on the same buffered domain, each providing

1. the original metric `r⁻²g`, exact coordinate and centre normalization, active support set and
   count, and the smooth domain;
2. separate original derivative-test domains, separation thresholds, a permitted short length `t`,
   permitted long lengths `s`, every inclusion needed by FC22, `ℓ₀ > t` (domains are the packets'
   fixed original domains: a quality change does not enlarge them);
3. AC76/AC79 compatibility on the short buffer and FC21's single coisometry (TCP02: `tcp02_row`,
   `tcp02_rowZ`);
4. uniform `C¹` comparison errors (TCP03: `tcp03_circle_row`, `tcp03_edge_row`, `tcp03_slim_row`,
   `tcp03_zero_row`; TCP04: `tcp04_row`).

Items 3–4 are the accepted TCP02–TCP04 rows. This module states items 1–2 on the final family's
ancestor `LocalChartPackets`, with the binding matrix of B:1530–1538 (two-stratum: original adapted
test, short `t = 400ρ(i)` chosen before `Δ`; edge / slim: own long axis test, shortened at the
reference distance `400ρ(i)`):

* `ScaledGeodesicReaches_RFC g hmetric x w₀ z`: for every normalized scale `R`, the geodesic of
  `R⁻²g` with initial velocity `Rw₀` reaches `z` at time `R⁻¹d(x, z)` (the form in which the
  packets' original derivative tests are applied).
* `fc23_circle_tests_RFC` (FC19 route, two long tests): for a unit `ξ`, a common long endpoint `y`
  in BOTH original far-test balls `B(·, 201·10⁴ρ)`, `x` in both near balls `B(·, 200ρ)`, length
  above both separation thresholds `201ρ`, `397ρ(i) ≤ d(x, y) ≤ (400 + 3β₂)ρ(i)`,
  `‖u_i(y) − u_i(x) − 400ξ‖ < 2β₂`, `y` in the (TR) ball `B(i, 1000ρ(i))`.
* `fc23_edge_tests_RFC`, `fc23_slim_tests_RFC` (FC22 route): the chart's OWN long test (near ball,
  far ball, separation threshold, long length `s = 200Δρ(j)` resp. `10·10⁶Δρ(j)` with its raw-axis
  gain), the short point `z` at `t = 400ρ(i)` on the SAME minimizing segment with
  `z ∈ B(i, 410ρ(i))` (the reference circle's far-test ball and the (TR) ball), `201ρ(i) < t` and
  `t < ℓ₀ = (s − 3b)`.
* ROW `fc23_items12_circle_RFC`: at every circle centre `i`, item 1 (TCP01's comparison list:
  count of ALL active supports, ratios, smooth original coordinates on `D_i`, zero assertions, the
  reference coordinate's quality and enclosure) and item 2 for every listed circle, edge and slim
  chart (closed support meeting `D_i`) and every `x ∈ D_i`.
* Consumer `fc23_edge_short_long_RFC` (the FC22 length data of item 2: `0 < t < ℓ₀ ≤ ℓ`).

The zero radial block (FC13's shell and LC73's radial test, `R₀/r` retained) is item 2 of
`tcp03_zero_row`'s proof (`zero_component_saturation_KA5`, reference lift of length `400`); it is
not restated here (see the state file).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X]

/-- The normalized-geodesic form of "`w₀` is the initial direction of a minimizing segment from
`x` through `z`": for every scale `R > 0`, the intrinsic geodesic of `R⁻²g` with initial velocity
`Rw₀` reaches `z` at time `R⁻¹d(x, z)`. -/
def ScaledGeodesicReaches_RFC (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (x : X)
    (w₀ : TangentSpace 𝓘(ℝ, E3) x) (z : X) : Prop :=
  ∀ (R : ℝ) (hR : 0 < R),
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
    letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
      isMetricNorm_of_riemannianBundle gR
    intrinsicGeodesic gR hnR x (R • w₀) (dist x z) = z

variable {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_RFC23
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_RFC23
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_RFC23
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC23 item 2, circle chart (FC19 route)**: at `x ∈ D_i` for a listed circle chart `j`
(ratio in `(.99, 1.01)`, `d(j, i) ≤ 214ρ(i)`, `x ∈ B(j, 200ρ(j))`, `β₂ ≤ 1/1000`) and a unit `ξ`:
one long endpoint `y` and a `g`-unit `w₀` reaching it, with `x` in both near-test balls, `y` in
both far-test balls, the length above both separation thresholds, the reference gain
`‖u_i(y) − u_i(x) − 400ξ‖ < 2β₂` and `y` in the (TR) ball. -/
theorem fc23_circle_tests_RFC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i j : X} (hi : i ∈ P.circle.centres) (hs : ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100))
    (hdij : dist j i ≤ 214 * ρ i) {x : X} (hx : x ∈ ball i (10 * ρ i))
    (hβ : β 2 ≤ 1 / 1000) (ξ : ℝ²) (hξ : ‖ξ‖ = 1) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
      397 * ρ i ≤ dist x y ∧ dist x y ≤ (400 + 3 * β 2) * ρ i ∧
      ‖circleRaw_KA3 P i y - circleRaw_KA3 P i x - (400 : ℝ) • ξ‖ < 2 * β 2 ∧
      x ∈ ball i (200 * ρ i) ∧ y ∈ ball i (201 * 10000 * ρ i) ∧
      y ∈ ball j (201 * 10000 * ρ j) ∧ 201 * ρ i < dist x y ∧ 201 * ρ j < dist x y ∧
      y ∈ ball i (1000 * ρ i) := by
  have hri := hρ i
  obtain ⟨hs1, hs2⟩ := hs
  have hrj1 : ρ j < 101 / 100 * ρ i := by rwa [div_lt_iff₀ hri] at hs2
  have hrj2 : 99 / 100 * ρ i < ρ j := by rwa [lt_div_iff₀ hri] at hs1
  obtain ⟨y, hD1, hD2, hyi, hlift⟩ := circle_reference_lift_KA4 P hi hx hβ ξ hξ
  have hxi : dist x i < 10 * ρ i := mem_ball.mp hx
  have hDpos : 0 < dist x y := by linarith
  have hxy : x ≠ y := fun h => by rw [h, dist_self] at hDpos; exact lt_irrefl _ hDpos
  obtain ⟨w₀, hw₀, hseg⟩ := exists_scaled_minimizing_seg_KA4 g hmetric hxy
  obtain ⟨y', -, hy'y, hgy⟩ := hseg (dist x y) dist_nonneg le_rfl
  have hyy : y' = y := dist_le_zero.mp (by linarith)
  rw [hyy] at hgy
  refine ⟨y, w₀, hw₀, hgy, hD1, hD2, hlift, by rw [mem_ball]; linarith,
    by rw [mem_ball]; linarith, ?_, by linarith, by linarith, by rw [mem_ball]; linarith⟩
  rw [mem_ball]
  have := dist_triangle y i j
  rw [dist_comm i j] at this
  linarith

/-- **FC23 item 2, edge chart (FC22 route)**: at `x ∈ D_i` for a listed edge chart `j` (ratio in
`(.99, 1.01)`, `x ∈ B(j, (14Δ + 40)ρ(j))`, `Δ ≥ 3`, `b ≤ 1/(1000Δ)`): the edge chart's OWN long
test along a `g`-unit `w₀` (near ball `B(j, 100Δρ(j))`, far ball `B(j, 1000Δρ(j))`, separation
`100Δρ(j)`, long length `s = 200Δρ(j)` up to `3bρ(j)` with raw-axis gain `200Δ` up to `2b`) and,
on the SAME minimizing segment, the short point `z` at `t = 400ρ(i)` in `B(i, 410ρ(i))`, with
`201ρ(i) < t < ℓ₀ = (200Δ − 3b)ρ(j)`. -/
theorem fc23_edge_tests_RFC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i j : X} (hj : j ∈ P.edge.centres) (hs : ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100))
    {x : X} (hx : x ∈ ball i (10 * ρ i)) (hxj : x ∈ ball j ((14 * Δ + 4 * 10) * ρ j))
    (hΔ : 3 ≤ Δ) (hb : b ≤ 1 / (1000 * Δ)) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
      x ∈ ball j (100 * Δ * ρ j) ∧ y ∈ ball j (1000 * Δ * ρ j) ∧
      100 * Δ * ρ j < dist x y ∧
      (200 * Δ - 3 * b) * ρ j ≤ dist x y ∧ dist x y ≤ (200 * Δ + 3 * b) * ρ j ∧
      |edgeRaw_KA3 P.toLocalChartFamily j y - edgeRaw_KA3 P.toLocalChartFamily j x - 200 * Δ| <
        2 * b ∧
      x ∈ ball i (200 * ρ i) ∧ 201 * ρ i < 400 * ρ i ∧ 400 * ρ i < (200 * Δ - 3 * b) * ρ j ∧
      ∃ z : X, dist x z = 400 * ρ i ∧ dist z y = dist x y - 400 * ρ i ∧
        z ∈ ball i (410 * ρ i) ∧ ScaledGeodesicReaches_RFC g hmetric x w₀ z := by
  have hri := hρ i
  have hrj := hρ j
  have hrj2 : 99 / 100 * ρ i < ρ j := by have := hs.1; rwa [lt_div_iff₀ hri] at this
  have hbpos : 0 < b := by
    obtain ⟨Y, mY, q, f, -⟩ := exists_edge_split_KA3 P.toLocalChartFamily hj
    exact @KleinerLottApprox.error_pos X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _ f
  have hΔ0 : 0 < Δ := by linarith
  have hbinv : 1000 * Δ ≤ b⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hbpos]
    rwa [one_div] at hb
  have hb1 : b ≤ 1 / 1000 := hb.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  have hxjd : dist x j < (14 * Δ + 4 * 10) * ρ j := mem_ball.mp hxj
  obtain ⟨y, hdxy, hlift, hyj⟩ := edge_lift_KA4 P.toLocalChartFamily hj (t := 200 * Δ) hxjd
    (by positivity) (by linarith)
  have hD1 : (200 * Δ - 3 * b) * ρ j ≤ dist x y := by
    have h' : 200 * Δ - 3 * b ≤ (ρ j)⁻¹ * dist x y := by linarith [(abs_le.mp hdxy).1]
    have := (le_inv_mul_iff₀ hrj).mp h'
    linarith
  have hD2 : dist x y ≤ (200 * Δ + 3 * b) * ρ j := by
    have h' : (ρ j)⁻¹ * dist x y ≤ 200 * Δ + 3 * b := by linarith [(abs_le.mp hdxy).2]
    have := (inv_mul_le_iff₀ hrj).mp h'
    linarith
  have hDpos : 0 < dist x y := lt_of_lt_of_le (by nlinarith) hD1
  have hxy : x ≠ y := fun h => by rw [h, dist_self] at hDpos; exact lt_irrefl _ hDpos
  have ht : 400 * ρ i < (200 * Δ - 3 * b) * ρ j := by nlinarith
  have h400 : 400 * ρ i ≤ dist x y := by linarith
  obtain ⟨w₀, hw₀, hseg⟩ := exists_scaled_minimizing_seg_KA4 g hmetric hxy
  obtain ⟨z, hxz, hzy, hgz⟩ := hseg (400 * ρ i) (by positivity) h400
  obtain ⟨y', -, hy'y, hgy⟩ := hseg (dist x y) dist_nonneg le_rfl
  have hyy : y' = y := dist_le_zero.mp (by linarith)
  rw [hyy] at hgy
  have hx100 : x ∈ ball j (100 * Δ * ρ j) := by rw [mem_ball]; nlinarith
  have hy1000 : y ∈ ball j (1000 * Δ * ρ j) := by
    rw [mem_ball]
    have h' : (ρ j)⁻¹ * dist y j < 1000 * Δ := by linarith
    have := (inv_mul_lt_iff₀ hrj).mp h'
    linarith
  have hxi : dist x i < 10 * ρ i := mem_ball.mp hx
  have hzi : z ∈ ball i (410 * ρ i) := by
    rw [mem_ball]
    have := dist_triangle z x i
    rw [dist_comm z x] at this
    linarith
  refine ⟨y, w₀, hw₀, hgy, hx100, hy1000, by nlinarith, hD1, hD2, hlift,
    by rw [mem_ball]; linarith, by linarith, ht, z, hxz, hzy, hzi, hgz⟩

/-- **FC23 item 2, slim chart (FC22 route)**: at `x ∈ D_i` for a listed slim chart `j` (ratio in
`(.99, 1.01)`, `x ∈ B(j, (.91L + 40)ρ(j))`, `L = 10⁶Δ`, `Δ ≥ 1`, `0 < σ_s ≤ 1/12`,
`β₁ ≤ 1/(100L)`): the slim chart's OWN long test (near ball `B(j, Lρ(j))`, far ball
`B(j, (L/σ_s)ρ(j))`, separation `Lρ(j)`, long length `s = 10Lρ(j)` up to `3β₁ρ(j)`, raw-axis gain
`10L` up to `2β₁`) and the short point `z` at `t = 400ρ(i)` on the SAME minimizing segment, with
`201ρ(i) < t < ℓ₀ = (10L − 3β₁)ρ(j)`. -/
theorem fc23_slim_tests_RFC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i j : X} (hj : j ∈ P.slim.centres) (hs : ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100))
    {x : X} (hx : x ∈ ball i (10 * ρ i))
    (hxj : x ∈ ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j)) (hΔ : 1 ≤ Δ)
    (hσs : 0 < σs) (hσs12 : σs ≤ 1 / 12) (hb : β 1 ≤ 1 / (100 * (10 ^ 6 * Δ))) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
      x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) ∧
      10 ^ 6 * Δ * ρ j < dist x y ∧
      (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ≤ dist x y ∧
      dist x y ≤ (10 * (10 ^ 6 * Δ) + 3 * β 1) * ρ j ∧
      |slimRaw_KA3 P.toLocalChartFamily j y - slimRaw_KA3 P.toLocalChartFamily j x -
        10 * (10 ^ 6 * Δ)| < 2 * β 1 ∧
      x ∈ ball i (200 * ρ i) ∧ 201 * ρ i < 400 * ρ i ∧
      400 * ρ i < (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ∧
      ∃ z : X, dist x z = 400 * ρ i ∧ dist z y = dist x y - 400 * ρ i ∧
        z ∈ ball i (410 * ρ i) ∧ ScaledGeodesicReaches_RFC g hmetric x w₀ z := by
  have hri := hρ i
  have hrj := hρ j
  have hrj2 : 99 / 100 * ρ i < ρ j := by have := hs.1; rwa [lt_div_iff₀ hri] at this
  have hbpos : 0 < β 1 := by
    let Sj := P.slim.centre j hj
    let _ := Sj.instZ
    exact @KleinerLottApprox.error_pos X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _ Sj.split
  have hΔ0 : 0 < Δ := by linarith
  have hL : (1000000 : ℝ) ≤ 10 ^ 6 * Δ := by linarith
  have hbinv : 100 * (10 ^ 6 * Δ) ≤ (β 1)⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hbpos]
    rwa [one_div] at hb
  have hb1 : β 1 ≤ 1 / 1000 := hb.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  have hxjd : dist x j < (91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j := mem_ball.mp hxj
  obtain ⟨y, hdxy, hlift, hyj⟩ := slim_lift_KA5 P.toLocalChartFamily hj
    (t := 10 * (10 ^ 6 * Δ)) hxjd (by positivity) (by linarith)
  have hD1 : (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ≤ dist x y := by
    have h' : 10 * (10 ^ 6 * Δ) - 3 * β 1 ≤ (ρ j)⁻¹ * dist x y := by
      linarith [(abs_le.mp hdxy).1]
    have := (le_inv_mul_iff₀ hrj).mp h'
    linarith
  have hD2 : dist x y ≤ (10 * (10 ^ 6 * Δ) + 3 * β 1) * ρ j := by
    have h' : (ρ j)⁻¹ * dist x y ≤ 10 * (10 ^ 6 * Δ) + 3 * β 1 := by
      linarith [(abs_le.mp hdxy).2]
    have := (inv_mul_le_iff₀ hrj).mp h'
    linarith
  have ht : 400 * ρ i < (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j := by nlinarith
  have hDpos : 0 < dist x y := lt_of_lt_of_le (by positivity) (ht.le.trans hD1)
  have hxy : x ≠ y := fun h => by rw [h, dist_self] at hDpos; exact lt_irrefl _ hDpos
  have h400 : 400 * ρ i ≤ dist x y := by linarith
  obtain ⟨w₀, hw₀, hseg⟩ := exists_scaled_minimizing_seg_KA4 g hmetric hxy
  obtain ⟨z, hxz, hzy, hgz⟩ := hseg (400 * ρ i) (by positivity) h400
  obtain ⟨y', -, hy'y, hgy⟩ := hseg (dist x y) dist_nonneg le_rfl
  have hyy : y' = y := dist_le_zero.mp (by linarith)
  rw [hyy] at hgy
  have hxL : x ∈ ball j (10 ^ 6 * Δ * ρ j) := by rw [mem_ball]; nlinarith
  have hyL : y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) := by
    rw [mem_ball]
    have h12 : 12 * (10 ^ 6 * Δ) ≤ 10 ^ 6 * Δ / σs := by
      rw [le_div_iff₀ hσs]
      nlinarith
    have h' : (ρ j)⁻¹ * dist y j < 10 ^ 6 * Δ / σs := by linarith
    have := (inv_mul_lt_iff₀ hrj).mp h'
    linarith
  have hxi : dist x i < 10 * ρ i := mem_ball.mp hx
  have hzi : z ∈ ball i (410 * ρ i) := by
    rw [mem_ball]
    have := dist_triangle z x i
    rw [dist_comm z x] at this
    linarith
  refine ⟨y, w₀, hw₀, hgy, hxL, hyL, by nlinarith, hD1, hD2, hlift,
    by rw [mem_ball]; linarith, by linarith, ht, z, hxz, hzy, hzi, hgz⟩

/-- **FC23 items 1–2 at the two-stratum base** (`found:fibration-original-binding`, B:1505–1538) on
`LocalChartPackets`, with FC07's ranges and the TCP03 bounds `Δ ≥ 3`, `b ≤ 1/(1000Δ)`,
`β₁ ≤ 1/(100·10⁶Δ)`, `0 < σ_s ≤ 1/12`, `β₂ ≤ 1/1000`. At every circle centre `i`:
item 1 = TCP01's comparison list on `D_i` (count of ALL active supports, ratios, smooth
original coordinates, zero assertions, the reference coordinate's quality and enclosure); item 2 =
for every listed circle / edge / slim chart `j` (closed support meeting `D_i`) and every
`x ∈ D_i`, the test configuration of `fc23_circle_tests_RFC` (both long tests, every unit `ξ`)
resp. `fc23_edge_tests_RFC`, `fc23_slim_tests_RFC` (own long test + short reference point at
`400ρ(i)`). -/
theorem fc23_items12_circle_RFC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 3 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hb : b ≤ 1 / (1000 * Δ))
    (hβ1 : β 1 ≤ 1 / (100 * (10 ^ 6 * Δ))) (hσs : 0 < σs) (hσs12 : σs ≤ 1 / 12)
    (hβ2 : β 2 ≤ 1 / 1000) {i : X} (hi : i ∈ P.circle.centres) :
    ((({j | j ∈ P.circle.centres ∧
          (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard : ℝ) +
        {j | j ∈ P.slim.centres ∧
          (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard +
        {j | j ∈ P.edge.centres ∧
          (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard +
        (zeroMeetingList P.zero i 10).ncard ≤ fc07ActiveBound) ∧
    (∀ j (hj : j ∈ P.circle.centres), (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (cgpCircleCoord P.toLocalChartFamily j hj)
          (ball i (10 * ρ i))) ∧
    (∀ j (hj : j ∈ P.slim.centres), (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.slim.centre j hj).coord (ball i (10 * ρ i))) ∧
    (∀ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.edge.coord j) (ball i (10 * ρ i))) ∧
    (∀ k ∈ zeroMeetingList P.zero i 10, ∀ k' ∈ zeroMeetingList P.zero i 10, k = k') ∧
    (∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
      (∀ x ∈ ball i (10 * ρ i), 3 / 20 * (P.zero.zero k hk).radius < dist k x ∧
        dist k x < 19 / 20 * (P.zero.zero k hk).radius) ∧
      ∃ O : Set X, IsOpen O ∧ ball i (10 * ρ i) ⊆ O ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.zero.zero k hk).radial O) ∧
    (∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x -
        circleSplitFst_KA2 P i hi x‖ < γ) ∧
    (∀ y ∈ ball i (200 * ρ i), ∀ z ∈ ball i (200 * ρ i),
      ‖cgpCircleCoord P.toLocalChartFamily i hi y - cgpCircleCoord P.toLocalChartFamily i hi z‖ ≤
        (1 + γ) / ρ i * dist y z) ∧
    (∀ q ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi q‖ ≤ 8 →
      q ∈ ball i (102 * ρ i))) ∧
    (∀ j ∈ P.circle.centres, (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∀ x ∈ ball i (10 * ρ i), x ∈ ball j (200 * ρ j) ∧ ∀ ξ : ℝ², ‖ξ‖ = 1 →
      ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
        ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
        397 * ρ i ≤ dist x y ∧ dist x y ≤ (400 + 3 * β 2) * ρ i ∧
        ‖circleRaw_KA3 P i y - circleRaw_KA3 P i x - (400 : ℝ) • ξ‖ < 2 * β 2 ∧
        x ∈ ball i (200 * ρ i) ∧ y ∈ ball i (201 * 10000 * ρ i) ∧
        y ∈ ball j (201 * 10000 * ρ j) ∧ 201 * ρ i < dist x y ∧ 201 * ρ j < dist x y ∧
        y ∈ ball i (1000 * ρ i)) ∧
    (∀ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∀ x ∈ ball i (10 * ρ i),
      ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
        ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
        x ∈ ball j (100 * Δ * ρ j) ∧ y ∈ ball j (1000 * Δ * ρ j) ∧
        100 * Δ * ρ j < dist x y ∧
        (200 * Δ - 3 * b) * ρ j ≤ dist x y ∧ dist x y ≤ (200 * Δ + 3 * b) * ρ j ∧
        |edgeRaw_KA3 P.toLocalChartFamily j y - edgeRaw_KA3 P.toLocalChartFamily j x - 200 * Δ| <
          2 * b ∧
        x ∈ ball i (200 * ρ i) ∧ 201 * ρ i < 400 * ρ i ∧ 400 * ρ i < (200 * Δ - 3 * b) * ρ j ∧
        ∃ z : X, dist x z = 400 * ρ i ∧ dist z y = dist x y - 400 * ρ i ∧
          z ∈ ball i (410 * ρ i) ∧ ScaledGeodesicReaches_RFC g hmetric x w₀ z) ∧
    (∀ j ∈ P.slim.centres, (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∀ x ∈ ball i (10 * ρ i),
      ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
        ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
        x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ y ∈ ball j (10 ^ 6 * Δ / σs * ρ j) ∧
        10 ^ 6 * Δ * ρ j < dist x y ∧
        (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ≤ dist x y ∧
        dist x y ≤ (10 * (10 ^ 6 * Δ) + 3 * β 1) * ρ j ∧
        |slimRaw_KA3 P.toLocalChartFamily j y - slimRaw_KA3 P.toLocalChartFamily j x -
          10 * (10 ^ 6 * Δ)| < 2 * β 1 ∧
        x ∈ ball i (200 * ρ i) ∧ 201 * ρ i < 400 * ρ i ∧
        400 * ρ i < (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ∧
        ∃ z : X, dist x z = 400 * ρ i ∧ dist z y = dist x y - 400 * ρ i ∧
          z ∈ ball i (410 * ρ i) ∧ ScaledGeodesicReaches_RFC g hmetric x w₀ z) := by
  have hΔ1 : 1 ≤ Δ := by linarith
  have hγ := circle_quality_nonneg_KA4 P hi
  have h1 := tcp01_row P hΛ hΔ1 hμ hτ hLΛ hLmax he hT hγ hi
  obtain ⟨-, hC, hS, hE, -, -⟩ := fc07_input_packet P hΛ hΔ1 hμ hτ hLΛ hLmax he hT i
  refine ⟨h1, fun j hj hmeet x hx => ?_, fun j hj hmeet x hx => ?_, fun j hj hmeet x hx => ?_⟩
  · obtain ⟨-, hd, hsub, hsub', -⟩ := hC j hj hmeet
    refine ⟨hsub' (hsub hx), fun ξ hξ => ?_⟩
    exact fc23_circle_tests_RFC P hi (h1.2.1 j hj hmeet).1 (by linarith only [hd]) hx hβ2 ξ hξ
  · obtain ⟨-, -, hsub, -, -⟩ := hE j hj hmeet
    exact fc23_edge_tests_RFC P hj (h1.2.2.2.1 j hj hmeet).1 hx (hsub hx) hΔ hb
  · obtain ⟨-, -, -, hsub, -, -⟩ := hS j hj hmeet
    exact fc23_slim_tests_RFC P hj (h1.2.2.1 j hj hmeet).1 hx (hsub hx) hΔ1 hσs hσs12 hβ1

/-- **Consumer: FC22's length data from FC23 item 2** (edge charts): at every circle centre, every
listed edge chart and every `x ∈ D_i` admit a long length `ℓ = d(x, y)` and the short length
`t = 400ρ(i)` with `0 < t < ℓ₀ ≤ ℓ`, `ℓ₀ = (200Δ − 3b)ρ(j)` (B:1527 "Require `ℓ₀ > t`"). -/
theorem fc23_edge_short_long_RFC
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 3 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hb : b ≤ 1 / (1000 * Δ))
    (hβ1 : β 1 ≤ 1 / (100 * (10 ^ 6 * Δ))) (hσs : 0 < σs) (hσs12 : σs ≤ 1 / 12)
    (hβ2 : β 2 ≤ 1 / 1000) {i : X} (hi : i ∈ P.circle.centres) {j : X} (hj : j ∈ P.edge.centres)
    (hmeet : (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty)
    {x : X} (hx : x ∈ ball i (10 * ρ i)) :
    ∃ y : X, 0 < 400 * ρ i ∧ 400 * ρ i < (200 * Δ - 3 * b) * ρ j ∧
      (200 * Δ - 3 * b) * ρ j ≤ dist x y := by
  obtain ⟨-, -, hE, -⟩ := fc23_items12_circle_RFC P hΛ hΔ hμ hτ hLΛ hLmax he hT hb hβ1 hσs
    hσs12 hβ2 hi
  obtain ⟨y, -, -, -, -, -, -, hD1, -, -, -, -, ht, -⟩ := hE j hj hmeet x hx
  exact ⟨y, mul_pos (by norm_num) (hρ i), ht, hD1⟩

end DifferentialGeometry.Geometry.Collapse
