import DifferentialGeometry.Geometry.Fibration.ActualCircleGram
import DifferentialGeometry.Geometry.Fibration.ActualFirstComparisonListApplications

/-!
# TCP01 in full on `LocalChartPacketsR`

* `tcp01_rowR_gram`: `tcp01_rowR` (the residual enclosure `|η_i| ≤ 8 ⇒ D_i`, `s₀ ≥ T/20`, the whole
  list count and the zero uniqueness) together with the Gram clause `tcp01_gram` of the circle
  coordinate at every point of `B(i, 200ρ(i))` (for `β₂ ≤ 10⁻⁷`); the remaining TCP01 clauses (ratios,
  domains, zero shells, early quality) are `tcp01_row`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNRG_C14KA2
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNRG_C14KA2
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCRG_C14KA2
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP01 with its Gram clause** on `LocalChartPacketsR`, at a circle centre `i`. -/
theorem tcp01_rowR_gram
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hγ : 0 ≤ γ) (hεr : 0 ≤ εr)
    (hβ : β 2 ≤ 1 / 10000000) {i : X} (hi : i ∈ P.circle.centres) :
    (∀ q ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi q‖ ≤ 8 →
      q ∈ ball i (10 * ρ i)) ∧
    (∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
      T / 20 ≤ (P.zero.zero k hk).radius / ρ i) ∧
    ∀ x ∈ ball i (200 * ρ i),
      (∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
        ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w‖ ≤ 1 + γ) ∧
      ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 ∧
        ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w - ξ‖ < γ + β 2 ∧
        1 - (γ + β 2) <
          inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w) ξ := by
  obtain ⟨h1, h2, -⟩ := tcp01_rowR P hΛ hΔ hμ hτ hLΛ hLmax he hT hγ hεr hi
  exact ⟨h1, h2, fun x hx =>
    tcp01_gram P.toLocalChartPacketsD.toLocalChartPackets hγ hβ hi hx⟩

end DifferentialGeometry.Geometry.Collapse
