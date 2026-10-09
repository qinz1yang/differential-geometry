import DifferentialGeometry.Geometry.Fibration.ActualAdjustedScaleInputs
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumer of EDP01's original-map inputs on `LocalChartPacketsC14`

* `edp01_support_scale_C14`: EDP01's localization on the closed support of `χ = ψ₁ ∘ 𝓔⁰`
  (B:6697–6709): at every point `p` of `tsupport χ` there is ONE circle index `i` such that every
  first-cloud contributor `q` at `𝓔⁰(p)` has `|ρ(q) − R_i| ≤ 10ΛR_i`, `|ρ(p) − R_i| ≤ 10ΛR_i`
  (SC), and every convex combination of contributor scales is within `(80/3)Λρ(p)` of `ρ(p)`.
  Consumes `edp01_cutoff_GAFS`, `edp01_contributor_scale_GAFS`, `edp01_mean_value_GAFS`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14AS_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14AS_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14AS_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EDP01's localization on the closed support of `χ = ψ₁ ∘ 𝓔⁰`** (`LocalChartPacketsC14`): at
every `p ∈ tsupport χ` there is one circle index `i` with (SC) for EVERY first-cloud contributor
at `𝓔⁰(p)` and for `p`, and every convex combination of contributor scales within `(80/3)Λρ(p)` of
`ρ(p)` (`b = εc⁻¹`, `Σ ≤ εc/10000`). -/
theorem edp01_support_scale_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    {εc σ : ℝ} (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) :
    ∀ p ∈ tsupport (fun p => markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
        (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)
        (cgpGlobalMap P.toLocalChartFamily P.zero p)),
      ∃ i : P.circle.finite_centres.toFinset,
        (∀ q ∈ fc04Set P.toLocalChartFamily P.zero 8,
          (closedBall (cgpGlobalMap P.toLocalChartFamily P.zero q) (80 * εc⁻¹ * (σ * ρ q)) ∩
            ball (cgpGlobalMap P.toLocalChartFamily P.zero p) (8 * εc⁻¹ * (σ * ρ p))).Nonempty →
          |ρ q - ρ i.1| ≤ 10 * Λ * ρ i.1) ∧
        |ρ p - ρ i.1| ≤ 10 * Λ * ρ i.1 ∧
        ∀ (ι : Type) (J : Finset ι) (q : ι → X),
          (∀ y ∈ J, q y ∈ fc04Set P.toLocalChartFamily P.zero 8 ∧
            (closedBall (cgpGlobalMap P.toLocalChartFamily P.zero (q y))
                (80 * εc⁻¹ * (σ * ρ (q y))) ∩
              ball (cgpGlobalMap P.toLocalChartFamily P.zero p) (8 * εc⁻¹ * (σ * ρ p))).Nonempty) →
          ∀ w : ι → ℝ, (∀ y ∈ J, 0 ≤ w y) → ∑ y ∈ J, w y = 1 →
            |∑ y ∈ J, w y * ρ (q y) - ρ p| ≤ 80 / 3 * Λ * ρ p := by
  intro p hp
  obtain ⟨-, -, -, hsupp, -⟩ := edp01_cutoff_GAFS P.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT
    hσs hσs1 hσc hγc hεr
  obtain ⟨i, hpi, hηi⟩ := hsupp p hp
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hη7 : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ 7 := by linarith
  refine ⟨i, fun q hq hmeet => ?_, ?_, fun ι J q hq w hw0 hw1 => ?_⟩
  · exact (edp01_contributor_scale_GAFS P.toLocalChartPacketsR hΔ hΛ hsmall hε hσ hσε i hpi hη7 hq
      hmeet).1
  · exact abs_scale_sub_le_of_coord_GAFS P.toLocalChartPacketsR hΛ i hpi (by linarith)
  · exact edp01_mean_value_GAFS P.toLocalChartPacketsR hΔ hΛ hsmall hε hσ hσε i hpi hη7 J q hq w
      hw0 hw1

end DifferentialGeometry.Geometry.Collapse
