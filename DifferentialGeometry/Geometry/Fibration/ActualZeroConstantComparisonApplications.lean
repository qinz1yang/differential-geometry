import DifferentialGeometry.Geometry.Fibration.ActualZeroConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualConstantComparisonApplications

/-!
# Consumer of TCP03 (zero block): the strict `C¹` form with the native operator norm

* `tcp03_zero_c1_lt`: TCP03's literal `‖s₀ η₀ − λ₀ η_i‖_{C¹(D_i)} < θ` for the meeting zero block
  on `LocalChartPacketsZ` (`λ₀(a) = A₀a + s₀η₀(p_i)`, rank one as `t e₀`): value `< θ` and
  `‖s₀ Dη₀ e₀ − A₀ Dη_i‖ < θ` in the operator norm of `ρ(i)⁻² g`.
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
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ_TCP03ZA_KA5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ_TCP03ZA_KA5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ_TCP03ZA_KA5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP03 (zero block), literal `C¹` form**: the meeting zero block has one unit row
`A₀ : ℝ² → ℝ¹` with `|s₀(η₀ − η₀(p_i)) e₀ − A₀ η_i| < θ` on `D_i` and
`‖s₀ Dη₀ e₀ − A₀ Dη_i‖ < θ` in the operator norm of `ρ(i)⁻² g`. -/
theorem tcp03_zero_c1_lt {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
      (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V ζ Λz),
      0 ≤ Λ → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → β 1 ≤ η₁ → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres), ∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A₀ : ℝ² →L[ℝ] ℝ¹,
          A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x ∈ ball i (10 * ρ i),
            ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                  ((P.zero.zero k hk).radial x - (P.zero.zero k hk).radial i)) -
                A₀ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < θ ∧
            letI := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr (hρ i))
            ‖((P.zero.zero k hk).radius / ρ i) •
                  (mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x).smulRight
                    (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) -
                A₀.comp (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x)‖ <
              θ := by
  obtain ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, η₁, hη₁, hrow⟩ := tcp03_zero_row hθ hθ1 hν hν1
  refine ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P hΛ
    hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ2 hγ hβ1 hζ hζθ hεr hΛz hσL i hi k hk hmeet
  obtain ⟨A, hA, -, htc⟩ := hrow P hΛ hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ2 hγ hβ1 hζ hζθ hεr hΛz hσL
    i hi k hk hmeet
  refine ⟨A, hA, fun x hx => ⟨(htc x hx).1.trans_lt (by linarith), ?_⟩⟩
  refine opNorm_lt_of_pointwise_KA4 g (hρ i) _ (c := θ / 2) (by linarith) (by linarith) fun w => ?_
  have h := (htc x hx).2 w
  rw [sub_apply, smul_apply]
  convert h using 4
  · ext m
    fin_cases m
    simp
  · rfl

end DifferentialGeometry.Geometry.Collapse
