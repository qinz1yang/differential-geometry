import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraph
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# EGP06 on the final family: comparison and model clauses together

* `egp06_full_C14`: on every actual `LocalChartPacketsC14` (the final chapter-14 family) with the
  hypotheses of `egp06_row`, at every edge centre `i`: ONE choice of signs and translations for
  which the model `Φ_i` is smooth, takes values in `Q₂`, has `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C†`,
  `|v| ≤ ‖DΦ_i(a) v‖` (own block `(a, 1)`), and (EG) holds on the edge core. This is the input
  EGP07 (rank, normal error) and FC27's edge (CS) test consume.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_KC4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_KC4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_KC4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- **EGP06 on the final family, comparison and model together.** For `Δ ≥ 1`,
`β₂ ∈ (0, 10⁻⁶)`, `0 < eg < 1/100` there are `Lc, η₀ > 0` such that on every actual
`LocalChartPacketsC14` with the hypotheses of `egp06_row`, at every edge centre `i` there is ONE
choice of signs `|sgn_t| ≤ 1` and translations `c_t` for which `Φ_i = egpModelGraph L Z i sgn c` is
smooth, `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C†`, `|v| ≤ ‖DΦ_i(a) v‖`, `Φ_i` takes values in `Q₂`, and EGP06's (EG)
holds on the edge core. -/
theorem egp06_full_C14 {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
        σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
        ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        ∀ i ∈ P.edge.centres,
          ∃ sgn c : CGPTag P.toLocalChartFamily P.zero → ℝ, (∀ t, |sgn t| ≤ 1) ∧
            ContDiff ℝ ∞ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) ∧
            (∀ a, ‖fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) a‖ ≤
                egpGraphConst ∧
              ‖fderiv ℝ (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)) a‖ ≤
                egpGraphConst) ∧
            (∀ a v : ℝ, ‖v‖ ≤ ‖fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) a v‖) ∧
            (∀ a, blockRestrict (cgpQ2Tags P.toLocalChartFamily P.zero)
              (egpModelGraph P.toLocalChartFamily P.zero i sgn c a) =
                egpModelGraph P.toLocalChartFamily P.zero i sgn c a) ∧
            ∀ x ∈ ball i (100 * Δ * ρ i), |P.edge.coord i x| ≤ 8 * Δ →
              cgpHeight P.toLocalChartFamily x ≤ 8 * Δ →
              ‖(ρ i)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero) x -
                egpModelGraph P.toLocalChartFamily P.zero i sgn c (P.edge.coord i x)‖ < eg ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                    (cgpQ2Tags P.toLocalChartFamily P.zero)) x w -
                  fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
                    (P.edge.coord i x) (mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w)‖ < eg := by
  obtain ⟨Lc, η₀, hLc, hη₀, h6⟩ := egp06_row hΔ hβ₂ hβ₂1 heg heg1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr i hi
  obtain ⟨sgn, c, hsgn, hEG⟩ := h6 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz P.toLocalChartPacketsRVZ hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs
    he hT hTz hζ0 hζθ hζL hεr i hi
  obtain ⟨hsm, -, hQ, hbd⟩ := egp06_model P.toLocalChartPacketsR hΛ hΔ hLΛ hμ hτ he hT hi sgn c
    hsgn
  exact ⟨sgn, c, hsgn, hsm, hbd,
    fun a v => egpModelGraph_lower_bound P.toLocalChartFamily P.zero hi sgn c a v, hQ, hEG⟩

end DifferentialGeometry.Geometry.Collapse
