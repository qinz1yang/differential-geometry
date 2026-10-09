import DifferentialGeometry.Geometry.Fibration.ActualStageSmoothingRows
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneTypes

/-!
# Consumers of CFS14 / CFS15 on the actual stage clouds: the (CS) tests from the stage planes

The (CS) hypothesis of `cfs14_row_CFSA` / `cfs15_row_CFSA` is supplied by the producer: the enhanced
stage planes of lane C14-PLANES (`FirstStagePlanes_PLN`, `EdgeStagePlanes_PLN`,
`SlimStagePlanes_PLN`) carry FC27's (CS) for EVERY selection of preimages (`cloudy`), their own
total radius selection `A.rsel x₀` (`rsel_spec` from `rpre_spec`) and the stage dimension
(`dimension`). Hence, at their quality `Γ` and radius factor `Σ`:

* `cfs15_firstStagePlanes_CFSA`, `cfs15_edgeStagePlanes_CFSA`, `cfs15_slimStagePlanes_CFSA`: CFS15's
  native output on the stage cloud with radius `Σρ(A.rsel x₀ x)` and plane `A.plane`, for every
  `0 < Γ < θ₁` and `0 < Σ ≤ Ξ(Γ)/640`.
* `cfs14_firstStagePlanes_CFSA`: CFS14 at a fixed accuracy `ε` for first-stage planes of quality
  `Γ ≤ d_*`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14A_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14A_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14A_CFSA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **CFS15 on the first-stage planes**: for `0 < Γ < θ₁` and `0 < Σ ≤ Ξ(Γ)/640`, every
first-stage plane witness `A` of quality `Γ` gives the native output on `S₁` with radius
`Σρ(A.rsel x₀ x)` and plane `A.plane` (its (CS) is `A.cloudy`). -/
theorem cfs15_firstStagePlanes_CFSA (Kj : ℕ) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 →
        1000000 * Δ * Λ < 1 / 100000 →
        ∀ sg eg : ℝ, 0 < sg → sg ≤ Ξ Γ / 640 →
        ∀ (A : FirstStagePlanes_PLN P Γ sg eg) (x₀ : X),
        Nonempty (Cfs15StageOutput (gafStageDim 0) Kj (Ξ Γ) cw
          (gafCloud P.toLocalChartFamily P.zero 0) (gafCloudEnlarged P.toLocalChartFamily P.zero 0)
          (fun x => sg * ρ (A.rsel x₀ x)) A.plane) := by
  obtain ⟨θ₁, hθ₁, Ξ, hΞ, h⟩ := cfs15_row_CFSA 0 Kj
  refine ⟨θ₁, hθ₁, Ξ, hΞ, fun Γ hΓ hΓθ => ?_⟩
  have hcw := (h Γ hΓ hΓθ).2.2
  refine ⟨hcw.choose, hcw.choose_spec.1, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sg eg hsg hsgΞ A x₀
  have hsel := A.rsel_spec x₀
    (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0))
    (fun x => (A.rpre_spec x).2)
  exact hcw.choose_spec.2 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    vs ζ Λz P hΛ hΔ hμ hτ he hLΛ (A.rsel x₀) hsel sg hsg hsgΞ A.plane
    (fun x hx => (A.dimension x hx).1) (A.cloudy (A.rsel x₀) hsel)

/-- **CFS15 on the edge-stage planes** (as `cfs15_firstStagePlanes_CFSA`, stage `1`). -/
theorem cfs15_edgeStagePlanes_CFSA (Kj : ℕ) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 →
        1000000 * Δ * Λ < 1 / 100000 →
        ∀ sg eg : ℝ, 0 < sg → sg ≤ Ξ Γ / 640 →
        ∀ (A : EdgeStagePlanes_PLN P Γ sg eg) (x₀ : X),
        Nonempty (Cfs15StageOutput (gafStageDim 1) Kj (Ξ Γ) cw
          (gafCloud P.toLocalChartFamily P.zero 1) (gafCloudEnlarged P.toLocalChartFamily P.zero 1)
          (fun x => sg * ρ (A.rsel x₀ x)) A.plane) := by
  obtain ⟨θ₁, hθ₁, Ξ, hΞ, h⟩ := cfs15_row_CFSA 1 Kj
  refine ⟨θ₁, hθ₁, Ξ, hΞ, fun Γ hΓ hΓθ => ?_⟩
  have hcw := (h Γ hΓ hΓθ).2.2
  refine ⟨hcw.choose, hcw.choose_spec.1, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sg eg hsg hsgΞ A x₀
  have hsel := A.rsel_spec x₀
    (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1))
    (fun x => (A.rpre_spec x).2)
  exact hcw.choose_spec.2 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    vs ζ Λz P hΛ hΔ hμ hτ he hLΛ (A.rsel x₀) hsel sg hsg hsgΞ A.plane
    (fun x hx => (A.dimension x hx).1) (A.cloudy (A.rsel x₀) hsel)

/-- **CFS15 on the slim-stage planes** (as `cfs15_firstStagePlanes_CFSA`, stage `2`). -/
theorem cfs15_slimStagePlanes_CFSA (Kj : ℕ) :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ Ξ : ℝ → ℝ, Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 →
        1000000 * Δ * Λ < 1 / 100000 →
        ∀ sg eg : ℝ, 0 < sg → sg ≤ Ξ Γ / 640 →
        ∀ (A : SlimStagePlanes_PLN P Γ sg eg) (x₀ : X),
        Nonempty (Cfs15StageOutput (gafStageDim 2) Kj (Ξ Γ) cw
          (gafCloud P.toLocalChartFamily P.zero 2) (gafCloudEnlarged P.toLocalChartFamily P.zero 2)
          (fun x => sg * ρ (A.rsel x₀ x)) A.plane) := by
  obtain ⟨θ₁, hθ₁, Ξ, hΞ, h⟩ := cfs15_row_CFSA 2 Kj
  refine ⟨θ₁, hθ₁, Ξ, hΞ, fun Γ hΓ hΓθ => ?_⟩
  have hcw := (h Γ hΓ hΓθ).2.2
  refine ⟨hcw.choose, hcw.choose_spec.1, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sg eg hsg hsgΞ A x₀
  have hsel := A.rsel_spec x₀
    (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2))
    (fun x => (A.rpre_spec x).2)
  exact hcw.choose_spec.2 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    vs ζ Λz P hΛ hΔ hμ hτ he hLΛ (A.rsel x₀) hsel sg hsg hsgΞ A.plane
    (fun x hx => (A.dimension x hx).1) (A.cloudy (A.rsel x₀) hsel)

/-- **CFS14 on the first-stage planes**: at a fixed accuracy `0 < ε ≤ 1/10` and jet order `K`, a
first-stage plane witness of quality `0 < Γ ≤ d_*` with `128 ε⁻¹ Σ ≤ 1/5` gives the native output on
`S₁` with radius `Σρ(A.rsel x₀ x)` and plane `A.plane`. -/
theorem cfs14_firstStagePlanes_CFSA (Kj : ℕ) (εa : ℝ) (hεa : 0 < εa) (hεa10 : εa ≤ 1 / 10) :
    ∃ dstar : ℝ, 0 < dstar ∧ ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 →
        1000000 * Δ * Λ < 1 / 100000 →
        ∀ Γ sg eg : ℝ, 0 < Γ → Γ ≤ dstar → 0 < sg → 128 * εa⁻¹ * sg ≤ 1 / 5 →
        ∀ (A : FirstStagePlanes_PLN P Γ sg eg) (x₀ : X),
        Nonempty (Cfs15StageOutput (gafStageDim 0) Kj εa cw
          (gafCloud P.toLocalChartFamily P.zero 0) (gafCloudEnlarged P.toLocalChartFamily P.zero 0)
          (fun x => sg * ρ (A.rsel x₀ x)) A.plane) := by
  obtain ⟨dstar, hdstar, cw, hcw, h⟩ := cfs14_row_CFSA 0 Kj εa hεa hεa10
  refine ⟨dstar, hdstar, cw, hcw, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ Γ sg eg hΓ hΓd hsg hmo A x₀
  have hsel := A.rsel_spec x₀
    (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0))
    (fun x => (A.rpre_spec x).2)
  have hO := h X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ (A.rsel x₀) hsel sg hsg hmo A.plane (fun x hx => (A.dimension x hx).1) Γ hΓ
    hΓd (A.cloudy (A.rsel x₀) hsel)
  exact hO.elim fun O _ => ⟨O⟩

end DifferentialGeometry.Geometry.Collapse
