import DifferentialGeometry.Geometry.Fibration.ActualFirstComparisonList

/-!
# Consumers of TCP01

* `tcp01_eta_ratio`: on `LocalChartPacketsR`, every original point `q` of the circle chart at `i`
  with `|η_i(q)| ≤ 8` has comparable scale, `ρ(q)/ρ(i) ∈ (99/100, 101/100)` (TCP01's enclosure in
  `D_i` and slow variation, as used by TCP04).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNRA_C14KA2
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNRA_C14KA2
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCRA_C14KA2
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- Every original point `|η_i| ≤ 8` of the circle chart at `i` has `ρ(q)/ρ(i) ∈ (99/100, 101/100)`. -/
theorem tcp01_eta_ratio
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hγ : 0 ≤ γ) (hεr : 0 ≤ εr) {i : X}
    (hi : i ∈ P.circle.centres) {q : X} (hq : q ∈ ball i (200 * ρ i))
    (h8 : ‖cgpCircleCoord P.toLocalChartFamily i hi q‖ ≤ 8) :
    ρ q / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) := by
  have hD := (tcp01_rowR P hΛ hΔ hμ hτ hLΛ hLmax he hT hγ hεr hi).1 q hq h8
  have hΛ10 : Λ * 10 < 1 / 100 := by nlinarith
  exact ratio_mem_Ioo_of_lipschitz_KA2 hΛ P.lipschitz_scale (hρ i) (mem_ball.mp hD).le hΛ10

end DifferentialGeometry.Geometry.Collapse
