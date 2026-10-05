import DifferentialGeometry.Geometry.Fibration.ActualStageEdgeTest
import DifferentialGeometry.Geometry.Fibration.ActualStageCloudsApplications

/-!
# Consumer of FC27's edge test: CFS14 on the actual edge cloud

* `cfs14_edge_stage_GAF3`: with GAF01's moduli `θ, Ξ` (`cfs14_actual_stage_GAF2`), for every quality
  `Γ ∈ (0, 1)`, `Γ < θ₁` and (EP) with `Σ ≤ Ξ₁(Γ)/640`, the planes of `fc27_edge_test_GAF3` feed
  CFS14 on the actual edge cloud: for every selection of preimages, a smoothing `W ⊆ N_{Ξr}(S̃₂)`
  whose rescaled truncation at every core centre is `7Ξ/16`-close to the enlarged cloud's.
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

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF3f {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF3f {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF3f {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **Consumer: CFS14 on the actual edge cloud with the edge test's planes.** With GAF01's moduli
`θ, Ξ`: for every `Γ ∈ (0,1)` with `Γ < θ₁` and (EP) with `Σ ≤ Ξ₁(Γ)/640`, on the final family with
the edge test's hypotheses, for every selection of preimages over `S̃₂` there is a smoothing
`W ⊆ N_{Ξr}(S̃₂)` whose `r_x⁻¹`-rescaled truncation at every core centre is `7Ξ/16`-close to the
enlarged cloud's (closed radius-`Ξ⁻¹` ball). -/
theorem cfs14_edge_stage_GAF3 (Kj : ℕ) {Δ β₂ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ), 0 < θ 1 ∧
      ∀ Γ Sg eg : ℝ, Γ ∈ Ioo (0 : ℝ) 1 → Γ < θ 1 → 0 < Sg →
        Sg < min (Γ / 200) (Γ ^ 3 / (100 * egpGraphConst)) → Sg ≤ Ξ 1 Γ / 640 → 0 < eg →
        eg < min (1 / 100) (min (Γ * Sg / 100) (Sg / 1000)) →
        ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
          ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
            [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
            (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
            (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
            (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
            (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ
              δ εr e T V vs ζ Λz),
            b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
            1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
            σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
            μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
            σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
            vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
            1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
            ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
            εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
            ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
              cgpProjMap P.toLocalChartFamily P.zero
                (gafStageTags P.toLocalChartFamily P.zero 1) (sel x) = x) →
            ∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
              W ⊆ ⋃ q ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
                ball q (Ξ 1 Γ * (Sg * ρ (sel q))) ∧
              ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
                hausdorffEDist (((fun y => (Sg * ρ (sel x))⁻¹ • (y - x)) ''
                    gafCloudEnlarged P.toLocalChartFamily P.zero 1) ∩ closedBall 0 (Ξ 1 Γ)⁻¹)
                  (((fun y => (Sg * ρ (sel x))⁻¹ • (y - x)) '' W) ∩ closedBall 0 (Ξ 1 Γ)⁻¹) ≤
                  ENNReal.ofReal (7 * Ξ 1 Γ / 16) := by
  obtain ⟨θ, Ξ, hc⟩ := cfs14_actual_stage_GAF2 Kj
  refine ⟨θ, Ξ, (hc 1).1, fun Γ Sg eg hΓ hθΓ hS hSmin hSΞ heg hemin => ?_⟩
  have hst := (hc 1).2.2 Γ hΓ.1 hθΓ
  obtain ⟨-, hmain⟩ := hst
  have hedge := fc27_edge_test_GAF3 hΔ hβ₂ hβ₂1 hΓ hS hSmin heg hemin
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := hedge
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hb
    hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr sel hsel
  have hP := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr
  obtain ⟨plane, hdimQ, hcloud, -⟩ := hP
  exact hmain X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ (by linarith) hLΛ sel hsel Sg hS hSΞ plane (fun x hx => (hdimQ x hx).1)
    (hcloud sel hsel)

end DifferentialGeometry.Geometry.Collapse
