import DifferentialGeometry.Geometry.Fibration.ActualFullMarkerContributors

/-!
# Consumers of GAF04 on `LocalChartPackets`

`gaf04_packets`: on the final LC87 packets with FC07's range `10⁶ΔΛ < 10⁻⁵`, GAF04's exact-marker
clause holds on all three actual clouds of `𝓔⁰`: every contributor (closed `80bΣρ` ball meeting the
`8bΣρ` ball of a core point with `|η_i| ≤ 7ℓ_i`) has the FULL `i` marker `R_i` and lies within
`R_i/50`; this is GAF03's hypothesis "`J y = c`" for `J = v_i`, `c = R_i`.
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
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNF_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNF_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCF_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF04's exact contributor markers on the actual packets** (first, edge and slim clouds). -/
theorem gaf04_packets
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {εc σ : ℝ} (hε : 0 < εc)
    (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) :
    (∀ (i : P.circle.finite_centres.toFinset) (px pu : X), px ∈ ball i.1 (200 * ρ i.1) →
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) px‖ ≤ 7 →
      pu ∈ fc04Set P.toLocalChartFamily P.zero 8 →
      (closedBall (cgpGlobalMap P.toLocalChartFamily P.zero pu) (80 * εc⁻¹ * (σ * ρ pu)) ∩
        ball (cgpGlobalMap P.toLocalChartFamily P.zero px) (8 * εc⁻¹ * (σ * ρ px))).Nonempty →
      cgpMarker P.toLocalChartFamily P.zero (.inl i)
        (cgpGlobalMap P.toLocalChartFamily P.zero pu) = ρ i.1) ∧
    (∀ (i : P.edge.finite_centres.toFinset) (px pu : X), px ∈ ball i.1 (100 * Δ * ρ i.1) →
      |P.edge.coord i.1 px| ≤ 7 * Δ → cgpHeight P.toLocalChartFamily px ≤ 7 * Δ →
      pu ∈ fc27EdgeSet P.toLocalChartFamily 8 →
      (closedBall (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ2Tags P.toLocalChartFamily P.zero) pu) (80 * εc⁻¹ * (σ * ρ pu)) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) px)
          (8 * εc⁻¹ * (σ * ρ px))).Nonempty →
      cgpMarker P.toLocalChartFamily P.zero (.inr (.inr i))
        (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) pu) =
        ρ i.1) ∧
    (∀ (i : P.slim.finite_centres.toFinset) (px pu : X), px ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) →
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord px| ≤ 7 * 10 ^ 5 * Δ →
      pu ∈ fc27SlimSet P.toLocalChartFamily 8 →
      (closedBall (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) pu) (80 * εc⁻¹ * (σ * ρ pu)) ∩
        ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) px)
          (8 * εc⁻¹ * (σ * ρ px))).Nonempty →
      cgpMarker P.toLocalChartFamily P.zero (.inr (.inl i))
        (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) pu) =
        ρ i.1) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  refine ⟨fun i px pu h1 h2 h3 h4 => ?_, fun i px pu h1 h2 h3 h4 h5 => ?_,
    fun i px pu h1 h2 h3 h4 => ?_⟩
  · exact (gaf04_circle P.toLocalChartFamilyQ P.zero hΔ hΛ hsmall hε hσ hσε i h1 h2 h3 h4).2.2
  · exact (gaf04_edge P.toLocalChartFamily P.zero hΔ hΛ hsmall hε hσ hσε i h1 h2 h3 h4 h5).2.2
  · exact (gaf04_slim P.toLocalChartFamily P.zero hΔ hΛ hsmall hε hσ hσε i h1 h2 h3 h4).2.2

end DifferentialGeometry.Geometry.Collapse
