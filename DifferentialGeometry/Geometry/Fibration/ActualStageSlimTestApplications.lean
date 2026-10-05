import DifferentialGeometry.Geometry.Fibration.ActualStageSlimTest
import DifferentialGeometry.Geometry.Fibration.ActualStageCloudsApplications

/-!
# FC27's slim test on the final family, and its consumer CFS14 on the actual slim cloud

* `fc27_slim_test_C14_GAF3`: `fc27_slim_test_GAF3` on THE family of chapter 14,
  `LocalChartPacketsC14` (through `P.toLocalChartPacketsRVZ`).
* `cfs14_slim_stage_GAF3` (consumer): with GAF01's moduli `θ, Ξ` (`cfs14_actual_stage_GAF2`), for
  every quality `0 < Γ < min(1, θ₂)` and (CP) with `Σ ≤ Ξ₂(Γ)/640`, the planes of the slim test feed
  CFS14 on the actual slim cloud: for every selection of preimages, a smoothing `W ⊆ N_{Ξr}(S̃₃)`
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
local instance instMetricNC14_GAF3s {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF3s {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF3s {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC27's slim test on the final family** `LocalChartPacketsC14` (consumer of
`fc27_slim_test_GAF3`). -/
theorem fc27_slim_test_C14_GAF3 {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
            Module.finrank ℝ (plane x) = gafStageDim 2 ∧
              plane x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
          (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
              cgpProjMap P.toLocalChartFamily P.zero
                (gafStageTags P.toLocalChartFamily P.zero 2) (sel x) = x) →
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
              hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
                  ball x (sg * ρ (sel x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
            ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              x →
            let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
              1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
  obtain ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, h⟩ :=
    fc27_slim_test_GAF3 hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ
  refine ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
  exact h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    P.toLocalChartPacketsRVZ

/-- **Consumer: CFS14 on the actual slim cloud with the slim test's planes.** With GAF01's moduli
`θ, Ξ`: for every `0 < Γ < min(1, θ₂)` and (CP) with `Σ ≤ Ξ₂(Γ)/640`, on the final family with the
slim test's hypotheses and `μ, τ ≤ 1/100`, for every selection of preimages over `S̃₃` there is a
smoothing `W ⊆ N_{Ξr}(S̃₃)` whose `r_x⁻¹`-rescaled truncation at every core centre is
`7Ξ/16`-close to the enlarged cloud's (closed radius-`Ξ⁻¹` ball). -/
theorem cfs14_slim_stage_GAF3 (Kj : ℕ) {Δ β₂ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ), 0 < θ 2 ∧
      ∀ Γ sg eg : ℝ, 0 < Γ → Γ < 1 → Γ < θ 2 → 0 < sg → sg < Γ / 200 →
        sg < Γ ^ 3 / (100 * sgpGraphBound) → sg ≤ Ξ 2 Γ / 640 → 0 < eg → eg < 1 / 100 →
        eg < Γ * sg / 100 →
        ∃ θs : ℝ, 0 < θs ∧ θs < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
          ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
            [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
            (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
            (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
            (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
            (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ
              δ εr e T V vs ζ Λz),
            β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
            e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
            0 < σs → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
            0 < ζ → ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
            εr < θs / (100 * (1000000 * Δ)) → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
            ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
              cgpProjMap P.toLocalChartFamily P.zero
                (gafStageTags P.toLocalChartFamily P.zero 2) (sel x) = x) →
            ∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
              W ⊆ ⋃ q ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
                ball q (Ξ 2 Γ * (sg * ρ (sel q))) ∧
              ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
                hausdorffEDist (((fun y => (sg * ρ (sel x))⁻¹ • (y - x)) ''
                    gafCloudEnlarged P.toLocalChartFamily P.zero 2) ∩ closedBall 0 (Ξ 2 Γ)⁻¹)
                  (((fun y => (sg * ρ (sel x))⁻¹ • (y - x)) '' W) ∩ closedBall 0 (Ξ 2 Γ)⁻¹) ≤
                  ENNReal.ofReal (7 * Ξ 2 Γ / 16) := by
  obtain ⟨θ, Ξ, hc⟩ := cfs14_actual_stage_GAF2 Kj
  refine ⟨θ, Ξ, (hc 2).1, fun Γ sg eg hΓ hΓ1 hθΓ hsg hsgΓ hsgC hsgΞ heg heg1 hegΓ => ?_⟩
  have hst := (hc 2).2.2 Γ hΓ hθΓ
  obtain ⟨-, hmain⟩ := hst
  have hslim := fc27_slim_test_C14_GAF3 hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ
  obtain ⟨θs, hθs, hθs1, Lc, η₀, hLc, hη₀, hrow⟩ := hslim
  refine ⟨θs, hθs, hθs1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr hμ hτ sel hsel
  have hP := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  obtain ⟨plane, hdimQ, hcloud, -⟩ := hP
  exact hmain X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ (by linarith) hLΛ sel hsel sg hsg hsgΞ plane (fun x hx => (hdimQ x hx).1)
    (hcloud sel hsel)

end DifferentialGeometry.Geometry.Collapse
