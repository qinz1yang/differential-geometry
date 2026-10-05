import DifferentialGeometry.Geometry.Fibration.ActualSlimZeroComparison

/-!
# Consumer of SGP03's zero part: the zero block's derivative is bounded on all of `D_i`

On the thresholds of `sgp03_zero_row` (merged family `LocalChartPacketsRVZ`): at every point of
`D_i = B(i, .95Lρ(i))` met by the zero ball at `p₀ = k`, the rescaled radial function `U₀ = s₀η₀`
has `|dU₀(w)| ≤ (1 + σs + θ)√(ρ(i)⁻² g(w, w))` — the zero derivative bound of (SC) combined with the
`(1 + σs)`-Lipschitz bound of the reference coordinate `η_i` (the input of SGP04's zero block,
whose model derivative is `a₀`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricNRVZA_SGP3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instChartedNRVZA_SGP3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricCRVZA_SGP3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The zero block's derivative on `D_i`** (consumer of `sgp03_zero_row`): on its thresholds,
`|s₀ dη₀(w)| ≤ (1 + σs + θ)√(ρ(i)⁻² g(w, w))` at every point of a `D_i` met by the zero ball. -/
theorem sgp03_zero_abs_mvfderiv_le {Δ β₂ θ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 < E) (hEθ : E < θ ^ 2 / 10 ^ 6) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        ∀ i ∈ P.slim.centres, ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
          ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            |(P.zero.zero k hk).radius / ρ i *
                mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w| ≤
              (1 + σs + θ) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := sgp03_zero_row hΔ hβ₂ hβ₂1 hθ hθ1 hE hEθ
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr i hi k hk hmeet x hx w
  obtain ⟨a₀, ha₀, -, hD, -⟩ := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz P hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr i hi k hk hmeet
  have hri := hρ i
  have hxL : x ∈ ball i (10 ^ 6 * Δ * ρ i) := by
    refine ball_subset_ball ?_ hx
    have := mul_mul_le_mul_mul_SGP2 (k := 95 / 100) (k' := 1) (L := 1000000 * Δ) (by norm_num)
      (by positivity) hri.le
    norm_num at this ⊢
    linarith
  have h1 := hD x hx w
  have h2 := (P.slim.centre i hi).abs_mvfderiv_le_SGP2 hσs.le hxL w
  have haabs : |a₀| = 1 := by rcases ha₀ with rfl | rfl <;> norm_num
  have hsq : Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) =
      (ρ i)⁻¹ * Real.sqrt (g.inner x w w) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h3 : |a₀ * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| ≤
      (1 + σs) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
    rw [abs_mul, haabs, one_mul, hsq]
    linarith
  have h4 := abs_sub_abs_le_abs_sub
    ((P.zero.zero k hk).radius / ρ i * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w)
    (a₀ * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w)
  linarith

end DifferentialGeometry.Geometry.Collapse
