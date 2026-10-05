import DifferentialGeometry.Geometry.Fibration.ActualStageOneCutoff
import DifferentialGeometry.Geometry.Fibration.ActualBlockBudgets

/-!
# Consumers of GAF02's stage-one cutoff on the actual `𝓔⁰`

* `gaf02_stageOne_core_plateau`: on every circle core `B(c_i, 2ρ(c_i))` (the LC87 plateau) the
  source cutoff is one at `𝓔⁰(p)`, so the stage-one adjustment there is the full projection.
* `gaf02_stageOne_vanishing`: the source cutoff vanishes at `𝓔⁰(p)` unless some circle coordinate
  has `|η_i(p)| ≤ 13/2` on its domain (the stage leaves `𝓔⁰` unchanged elsewhere).
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
local instance instMetricNSA_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNSA_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCSA_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **Stage-one plateau on the circle cores**: `ψ₁(𝓔⁰ p) = 1` on `B(c_i, 2ρ(c_i))`. -/
theorem gaf02_stageOne_core_plateau
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (j : P.circle.finite_centres.toFinset) {p : X} (hp : p ∈ ball j.1 (2 * ρ j.1)) :
    markerLocalitySourceCutoff lc87EdgeTransition (fun i => ρ i.1) (gafCircleVector P)
      (gafCircleMarker P) (cgpGlobalMap P.toLocalChartFamily P.zero p) = 1 := by
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hrj := hρ j.1
  have hp200 : p ∈ ball j.1 (200 * ρ j.1) := ball_subset_ball (by linarith) hp
  have hj200 : j.1 ∈ ball j.1 (200 * ρ j.1) := mem_ball_self (by positivity)
  have hlip := cgpCircleCoord_lipschitz P.toLocalChartFamily hj p hp200 j.1 hj200
  have hcen : cgpCircleCoord P.toLocalChartFamily j.1 hj j.1 = 0 := by
    have hc := P.circle.chart_center j.1 hj
    let c := P.circle.chart j.1 hj
    let mR : MetricSpace X := mX.rescale (ρ j.1)⁻¹ (inv_pos.mpr (hρ j.1))
    have hc' : c.center = j.1 := hc
    have h0 := c.coord_center
    rw [hc'] at h0
    exact h0
  rw [hcen, sub_zero] at hlip
  have hd : dist p j.1 < 2 * ρ j.1 := hp
  have hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6 := by
    change ‖cgpCircleCoord P.toLocalChartFamily j.1 hj p‖ < 6
    have h4 : 2 / ρ j.1 * dist p j.1 < 2 / ρ j.1 * (2 * ρ j.1) :=
      mul_lt_mul_of_pos_left hd (by positivity)
    have h5 : 2 / ρ j.1 * (2 * ρ j.1) = 4 := by field_simp; ring
    linarith
  exact (gaf02_stageOne_sourceCutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1).2.2.1 p
    ⟨j, hp200, hη⟩

/-- **Stage one leaves `𝓔⁰` alone away from the circle charts**: `ψ₁(𝓔⁰ p) = 0` unless some circle
coordinate has `|η_i(p)| ≤ 13/2` on its domain `B(c_i, 200ρ(c_i))`. -/
theorem gaf02_stageOne_vanishing
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    {p : X} (hp : ∀ j : P.circle.finite_centres.toFinset, p ∈ ball j.1 (200 * ρ j.1) →
      13 / 2 < ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖) :
    markerLocalitySourceCutoff lc87EdgeTransition (fun i => ρ i.1) (gafCircleVector P)
      (gafCircleMarker P) (cgpGlobalMap P.toLocalChartFamily P.zero p) = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  obtain ⟨j, hj, hη⟩ :=
    (gaf02_stageOne_sourceCutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1).2.2.2.1 p hmem
  exact absurd hη (not_le.mpr (hp j hj))

end DifferentialGeometry.Geometry.Collapse
