import DifferentialGeometry.Geometry.Fibration.ActualFirstCloud
import DifferentialGeometry.Geometry.Fibration.ActualCloudPlaneCoherence

/-!
# Consumer of TCP06: CFS08 on FC07's first cloud with TCP06's planes

* `tcp06_first_cloud_coherence_C14`: the planes of `tcp06_row` feed `cfs08_first_cloud` (CFS08 on
  FC07's first cloud `S₁ = F(A₁) ⊆ S̃₁ = F(Ã₁)`, FC04's exact radius `r = Σx_ρ`) directly: for every
  scale `L' ≥ 1` with `L'Σ ≤ 1/5` and `Γ` below CFS08's threshold, (LC) holds for every pair of
  `S₁` at distance `≤ L' max(r(x), r(y))`; the planes are two-dimensional.
* The blueprint's verbatim (TP) (`Σ < min{Γ/200, Γ³/(100C)}`, `e < min{1/100, ΓΣ/100, Σ/1000}`) as
  an `example`; `e < Σ/1000` is not used (strengthening).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_TCP06A_KA8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_TCP06A_KA8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_TCP06A_KA8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- TCP06 with the blueprint's (TP) verbatim (`e < Σ/1000` is not needed). -/
example {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgmin : sg < min (Γ / 200) (Γ ^ 3 / (100 * tcpGraphConst))) (heg : 0 < eg)
    (hegmin : eg < min (1 / 100) (min (Γ * sg / 100) (sg / 1000))) (hν : 0 < ν) (hν1 : ν < 1) :=
  tcp06_row hΓ hΓ1 hsg (lt_min_iff.mp hsgmin).1 (lt_min_iff.mp hsgmin).2 heg
    (lt_min_iff.mp hegmin).1 (lt_min_iff.mp (lt_min_iff.mp hegmin).2).1 hν hν1

/-- **Consumer: CFS08 on FC07's first cloud with TCP06's planes.** Under `tcp06_row`'s thresholds
and hypotheses, the planes of TCP06 are two-dimensional on `S₁ = F(A₁)` and, for every scale
`L' ≥ 1` with `L'Σ ≤ 1/5` and `Γ` below CFS08's threshold, satisfy (LC) for every pair of `S₁` at
distance `≤ L' max(r(x), r(y))`, `r = Σx_ρ` (FC04's exact radius). -/
theorem tcp06_first_cloud_coherence_C14 {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst))
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧
    θ < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
          Module.finrank ℝ (plane x) = 2) ∧
        ∀ L' : ℝ, 1 ≤ L' → L' * sg ≤ 1 / 5 →
        Γ < min (1 / (4 * (5 / 3))) (min (1 / (2 * (L' * (5 / 3) + 3))) (1 / (4 * (5 / 3 + 1)))) →
        ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        ∀ y ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
          dist y x ≤ L' * max (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)
            (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg y) →
          ‖(plane x)ᗮ.starProjection (y - x)‖ ≤
              Γ * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x ∧
            ‖(plane x)ᗮ.starProjection - (plane y)ᗮ.starProjection‖ ≤ 6 * (5 / 3 + 1) * Γ := by
  have H := tcp06_row hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hν hν1
  refine Exists.elim H (fun σ hσ => ⟨σ, hσ.1, hσ.2.1, ?_⟩)
  refine Exists.elim hσ.2.2 (fun η₂ h₂ => ⟨η₂, ?_⟩)
  refine Exists.elim h₂ (fun γ₀ h₃ => ⟨γ₀, ?_⟩)
  refine Exists.elim h₃ (fun ηc h₄ => ⟨ηc, ?_⟩)
  refine Exists.elim h₄ (fun θ h₅ => ⟨θ, h₅.1, h₅.2.1, h₅.2.2.1, h₅.2.2.2.1, h₅.2.2.2.2.1,
    fun Δ hΔ => ?_⟩)
  refine Exists.elim (h₅.2.2.2.2.2 Δ hΔ) (fun η₁ h₆ => ⟨η₁, h₆.1, ?_⟩)
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    h26 h27 h28 h29 h30 h31
  have hP := h₆.2 P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
    h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  refine Exists.elim hP (fun plane hpl => ⟨plane, hpl.1, fun L' hL' hLsg hδsmall => ?_⟩)
  exact cfs08_first_cloud P.toLocalChartFamily P.zero hL' hsg hLsg plane hpl.1 hΓ hδsmall hpl.2.1

end DifferentialGeometry.Geometry.Collapse
