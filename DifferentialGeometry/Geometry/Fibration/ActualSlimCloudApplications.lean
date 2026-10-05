import DifferentialGeometry.Geometry.Fibration.ActualSlimCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# SGP06 on the final chapter-14 family, and its consumer CFS08

* `sgp06_row_C14`: `sgp06_row` on THE family of chapter 14, `LocalChartPacketsC14`
  (through `P.toLocalChartPacketsRVZ`; `εr < θ/(100L)` is discharged by the final producer
  `eventually_nonempty_localChartPacketsC14`).
* `sgp06_slim_coherence_C14`: the consumer — the planes of SGP06 feed `cfs08_slim_cloud` (CFS08 on
  FC27's slim cloud) directly: for every selection of preimages, every scale `L' ≥ 1` with
  `L'Σ ≤ 1/5` and `Γ` below CFS08's threshold, (LC) holds for every pair of `S₃` at distance
  `≤ L' max(r)`.
* The blueprint's verbatim (CP) (`Σ < min{Γ/200, Γ³/(100C_*)}`,
  `e < min{1/100, ΓΣ/100, Σ/1000}`) as an `example`; `e < Σ/1000` is not used (strengthening).
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
local instance instMetricNC14_SGP5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_SGP5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_SGP5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **SGP06 on the final family** `LocalChartPacketsC14` (consumer of `sgp06_row`). -/
theorem sgp06_row_C14 {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hΓ : 0 < Γ)
    (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
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
          (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
              fc27SlimSet P.toLocalChartFamily 7, Module.finrank ℝ (plane x) = 1) ∧
          (∀ select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
                fc27SlimSet P.toLocalChartFamily 8,
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
                (select x) = x) →
            ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
                fc27SlimSet P.toLocalChartFamily 7,
              hausdorffEDist (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ3Tags P.toLocalChartFamily P.zero) '' fc27SlimSet P.toLocalChartFamily 8 ∩
                  ball x (sg * ρ (select x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (sg * ρ (select x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (select x)))) ∧
          ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
              fc27SlimSet P.toLocalChartFamily 7,
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
    sgp06_row hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ
  refine ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
  exact h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    P.toLocalChartPacketsRVZ

/-- SGP06 with the blueprint's (CP) verbatim (`e < Σ/1000` is not needed). -/
example {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hΓ : 0 < Γ)
    (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgmin : sg < min (Γ / 200) (Γ ^ 3 / (100 * sgpGraphBound)))
    (heg : 0 < eg) (hegmin : eg < min (1 / 100) (min (Γ * sg / 100) (sg / 1000))) :=
  sgp06_row hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg (lt_min_iff.mp hsgmin).1 (lt_min_iff.mp hsgmin).2 heg
    (lt_min_iff.mp hegmin).1 (lt_min_iff.mp (lt_min_iff.mp hegmin).2).1

/-- FC07's parameter range gives CFS08's `Λ(10⁶Δ) ≤ 1/4`. -/
theorem lambda_le_quarter_SGP5 {Δ Λ : ℝ} (h : 1000000 * Δ * Λ < 1 / 100000) :
    Λ * (1000000 * Δ) ≤ 1 / 4 := by
  rw [mul_comm]
  linarith

/-- **Consumer: CFS08 on FC27's slim cloud with SGP06's planes.** On the final family, for every
selection of preimages over `S̃₃`, every scale `L' ≥ 1` with `L'Σ ≤ 1/5` and `Γ` below CFS08's
threshold, the planes of `sgp06_row_C14` satisfy (LC) for every pair of `S₃` at distance
`≤ L' max(r(x), r(y))`, `r = Σρ ∘ select`. -/
theorem sgp06_slim_coherence_C14 {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
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
          ∀ select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
                fc27SlimSet P.toLocalChartFamily 8,
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
                (select x) = x) →
            ∀ L' : ℝ, 1 ≤ L' → L' * sg ≤ 1 / 5 →
            Γ < min (1 / (4 * (5 / 3)))
              (min (1 / (2 * (L' * (5 / 3) + 3))) (1 / (4 * (5 / 3 + 1)))) →
            ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
                fc27SlimSet P.toLocalChartFamily 7,
            ∀ y ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
                fc27SlimSet P.toLocalChartFamily 7,
              dist y x ≤ L' * max (sg * ρ (select x)) (sg * ρ (select y)) →
              ‖(plane x)ᗮ.starProjection (y - x)‖ ≤ Γ * (sg * ρ (select x)) ∧
                ‖(plane x)ᗮ.starProjection - (plane y)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * Γ := by
  obtain ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, h⟩ :=
    sgp06_row_C14 hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ
  refine ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  have hP := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  obtain ⟨plane, hdim, hcloud, -⟩ := hP
  have hsmall := lambda_le_quarter_SGP5 hLΛ
  refine ⟨plane, fun select hselect L' hL' hLsg hδsmall => ?_⟩
  exact cfs08_slim_cloud P.toLocalChartFamily P.zero hΔ hΛ hsmall select hselect hL' hsg hLsg plane
    hdim hΓ hδsmall (hcloud select hselect)

end DifferentialGeometry.Geometry.Collapse
