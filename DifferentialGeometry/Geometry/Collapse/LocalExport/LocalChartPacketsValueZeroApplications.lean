import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsValueZeroProducer
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsValueApplications
import DifferentialGeometry.Geometry.Fibration.ActualZeroRawAlignment

/-!
# Consumer of the merged family: the zero alignment against the SMOOTH slim coordinate

On `P : LocalChartPacketsRVZ`, the slim block (LFR19's separate value tolerance `vs`, field
`slim_value` of the RV projection) and the zero block (SGP02's (R0), `sgp02_zero_supplier_ZERO` on
the Z projection) hold on the SAME family:

* `sgp02_zero_smooth_ZERO`: with the thresholds of (R0), at every slim centre `i` whose `D_i`
  meets the support of the zero ball at `p₀ = k`, a sign `a₀` with
  `|ρ(i)⁻¹ (d(p₀, x) − d(p₀, i)) − a₀ η_i(x)| < E + vs` on the smooth domain `B(i, Lρ(i))` of the
  ORIGINAL slim coordinate `η_i` (the value input of SGP03's zero analogue, B:4483–4490).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricNRVZ_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instChartedNRVZ_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricCRVZ_ZERO {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The zero alignment against the smooth slim coordinate on the merged family.** With the
thresholds `Lc`, `η₀` of SGP02's (R0): on every `P : LocalChartPacketsRVZ`, at every slim centre
`i` whose `D_i` meets the support of the zero ball at `k`, a sign `a₀` with
`|ρ(i)⁻¹ (d(k, x) − d(k, i)) − a₀ η_i(x)| < E + vs` on `B(i, 10⁶Δρ(i))`. -/
theorem sgp02_zero_smooth_ZERO {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        ∀ i (hi : i ∈ P.slim.centres), ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
          ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (10 ^ 6 * Δ * ρ i),
            |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * (P.slim.centre i hi).coord x| < E + vs := by
  obtain ⟨Lc, η₀, hLc, hη₀, hR0⟩ := sgp02_zero_supplier_ZERO hΔ hβ₂ hβ₂1 hE
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT i hi k hk hmeet
  obtain ⟨a₀, ha₀, hal⟩ := hR0 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V ζ Λz P.toLocalChartPacketsZ hβ2 hβ1 hLmax hΛ hLΛ he hT i hi k hk hmeet
  refine ⟨a₀, ha₀, fun x hx => ?_⟩
  have hri := hρ i
  have hx30 : x ∈ ball i (30 * (1000000 * Δ) * ρ i) := by
    refine ball_subset_ball ?_ hx
    nlinarith
  have h1 := hal x hx30
  have h2 := P.toLocalChartPacketsRV.slim_value_sgpRaw hi hx
  have ha : |a₀| = 1 := by rcases ha₀ with h | h <;> simp [h]
  have h3 : |a₀ * sgpRaw P.slim i x - a₀ * (P.slim.centre i hi).coord x| < vs := by
    rw [← mul_sub, abs_mul, ha, one_mul, abs_sub_comm]
    exact h2
  calc |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * (P.slim.centre i hi).coord x|
      ≤ |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * sgpRaw P.slim i x| +
        |a₀ * sgpRaw P.slim i x - a₀ * (P.slim.centre i hi).coord x| := abs_sub_le _ _ _
    _ < E + vs := add_lt_add h1 h3

end DifferentialGeometry.Geometry.Collapse
