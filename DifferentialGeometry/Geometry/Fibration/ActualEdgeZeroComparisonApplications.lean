import DifferentialGeometry.Geometry.Fibration.ActualEdgeZeroComparison

/-!
# The complete rows EGP03 and EGP04 (edge, slim and zero blocks under one threshold choice)

* `egp03_full_row`: EGP03 complete — (ER) for every `j ∈ J_e ∪ J_s` (`egp03_row`) and (ER0) for
  every zero support meeting `D_i` (`egp03_zero_supplier_egpRaw_ZERO`), under ONE choice of
  `Lc, η₀`,
  on every actual `LocalChartPacketsZ`.
* `egp04_row_RVZ`: EGP04 complete — `egp04_row`'s (EC) for `J_e ∪ J_s` and the zero block
  (`egp04_zero_row`) under ONE choice of thresholds, on every actual `LocalChartPacketsRVZ` (the
  smallest family carrying LFR19's slim tolerance and LC73's zero clauses; `LocalChartPacketsC14`
  projects to it).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZa_KC3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZa_KC3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZa_KC3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The model metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricNRVZa_KC3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instChartedNRVZa_KC3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricCRVZa_KC3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EGP03 complete on the actual family**: (ER) for every `j ∈ J_e ∪ J_s` and (ER0) for every
zero support meeting `D_i`, under ONE choice of the curvature radius `Lc` and the raw quality
`η₀`, on every actual `LocalChartPacketsZ`. -/
theorem egp03_full_row {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ)
        (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → ∀ i ∈ P.edge.centres,
          (∀ j ∈ egpEdgeList P.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * egpRaw P.edge j x - a * egpRaw P.edge i x -
                ρ j / ρ i * egpRaw P.edge j i| < E) ∧
          (∀ j ∈ egpSlimList P.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * sgpRaw P.slim j x - a * egpRaw P.edge i x -
                ρ j / ρ i * sgpRaw P.slim j i| < E) ∧
          ∀ k (hk : k ∈ P.zero.centres),
            (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
              ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
            ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (600 * Δ * ρ i),
              |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x| < E := by
  obtain ⟨L₁, η₁, hL₁, hη₁, h1⟩ := egp03_row hΔ hβ₂ hβ₂1 hE
  obtain ⟨L₂, η₂, hL₂, hη₂, h2⟩ := egp03_zero_supplier_egpRaw_ZERO hΔ hβ₂ hβ₂1 hE
  refine ⟨max L₁ L₂, min η₁ η₂, lt_max_of_lt_left hL₁, lt_min hη₁ hη₂, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P hb hs
    hβ1 hLmax hΛ hLΛ hμ hτ he hT i hi
  obtain ⟨he', hsl⟩ := h1 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ
    P.toLocalChartFamilyE (hb.trans (min_le_left _ _)) hs (hβ1.trans (min_le_left _ _))
    ((le_max_left _ _).trans hLmax) hΛ hLΛ hμ hτ i hi
  exact ⟨he', hsl, h2 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P
    (hb.trans (min_le_right _ _)) hs (hβ1.trans (min_le_right _ _))
    ((le_max_right _ _).trans hLmax) hΛ hLΛ he hT i hi⟩

/-- **EGP04 complete on the actual family**: for `0 < θ < 1` there are ONE curvature radius `Lc`
and ONE raw quality `η₀` such that on every actual `LocalChartPacketsRVZ` with the hypotheses of
`egp04_row` and of `egp04_zero_row`, at every edge centre `i`: (EC) for every `j ∈ J_e`, for
every slim chart meeting `D_i`, and for every zero support meeting `D_i`. -/
theorem egp04_row_RVZ {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → σc ≤ θ ^ 2 / 10 ^ 8 →
        μ * Δ < θ / 100 → 0 < σs → σs ≤ θ ^ 2 / 10 ^ 8 → vs < θ / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ → ζ ≤ θ ^ 2 / 10 ^ 8 →
        ζ ≤ 1 / (1000 * (1000000 * Δ)) → εr < θ / (100 * (1000000 * Δ)) →
        ∀ i ∈ P.edge.centres,
          (∀ j ∈ egpEdgeList P.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (20 * Δ * ρ i),
              |ρ j / ρ i * P.edge.coord j x -
                  (a * P.edge.coord i x + ρ j / ρ i * egpRaw P.edge j i)| < θ ∧
                ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                  |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.edge.coord j) x w -
                    a * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ) ∧
          (∀ j (hj : j ∈ P.slim.centres),
            (tsupport (P.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
            ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
              |ρ j / ρ i * (P.slim.centre j hj).coord x -
                  (a * P.edge.coord i x + ρ j / ρ i * sgpRaw P.slim j i)| < θ ∧
                ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                  |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord x w -
                    a * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ) ∧
          ∀ k (hk : k ∈ P.zero.centres),
            (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
              ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
            ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
              |(P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial x -
                  (a₀ * P.edge.coord i x +
                    (P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)| < θ ∧
                ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                  |(P.zero.zero k hk).radius / ρ i *
                      mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w -
                    a₀ * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ := by
  obtain ⟨L₁, η₁, hL₁, hη₁, h1⟩ := egp04_row hΔ hβ₂ hβ₂1 hθ hθ1
  obtain ⟨L₂, η₂, hL₂, hη₂, h2⟩ := egp04_zero_row hΔ hβ₂ hβ₂1 hθ hθ1
  refine ⟨max L₁ L₂, min η₁ η₂, lt_max_of_lt_left hL₁, lt_min hη₁ hη₂, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr i hi
  obtain ⟨he', hsl⟩ := h1 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
    P.toLocalChartPacketsRV (hb.trans (min_le_left _ _)) hs (hβ1.trans (min_le_left _ _))
    ((le_max_left _ _).trans hLmax) hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs i hi
  exact ⟨he', hsl, h2 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz
    P.toLocalChartPacketsZ (hb.trans (min_le_right _ _)) hs (hβ1.trans (min_le_right _ _))
    ((le_max_right _ _).trans hLmax) hΛ hLΛ he hT hTz hσc hμΔ hζ0 hζθ hζL hεr i hi⟩

end DifferentialGeometry.Geometry.Collapse
