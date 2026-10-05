import DifferentialGeometry.Geometry.Fibration.ActualStageCutoffs

/-!
# Consumers of GAF02's stage-two and stage-three cutoffs: stages leave far points alone

* `gaf02_stageTwo_vanishing`: for any `f` with CFS31's contract, `ψ₂(f p) = 0` unless the ORIGINAL
  point lies in the threshold-`7Δ` edge core (closed-support localization of `gaf02_stageTwo_cutoff`).
* `gaf02_stageThree_vanishing`: the same for `ψ₃` and the threshold-`7·10⁵Δ` slim core.
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
local instance instMetricNSTA_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNSTA_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCSTA_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **Stage two leaves far points alone**: `ψ₂(f p) = 0` unless the original point is in the
threshold-`7Δ` edge core. -/
theorem gaf02_stageTwo_vanishing
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hpert : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤
      4 * gafKappa / 5 * ρ p)
    (hZM : ∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) {p : X}
    (hp : ∀ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) →
      |P.edge.coord j.1 p| < 7 * Δ → 7 * Δ ≤ cgpHeight P.toLocalChartFamily p) :
    gafStageTwoCutoff P.toLocalChartFamily P.zero (f p) = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  obtain ⟨j, hj, hη, ht⟩ := (gaf02_stageTwo_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f
    hpert hZM).2.2.2.1 p hmem
  exact absurd ht (not_lt.mpr (hp j hj hη))

/-- **Stage three leaves far points alone**: `ψ₃(f p) = 0` unless the original point is in the
threshold-`7·10⁵Δ` slim core. -/
theorem gaf02_stageThree_vanishing
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hpert : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤
      4 * gafKappa / 5 * ρ p)
    (hZM : ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) {p : X}
    (hp : ∀ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) →
      7 * (10 ^ 5 * Δ) ≤ |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p|) :
    gafStageThreeCutoff P.toLocalChartFamily P.zero (f p) = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  obtain ⟨j, hj, hη⟩ := (gaf02_stageThree_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f
    hpert hZM).2.2.2.1 p hmem
  exact absurd hη (not_lt.mpr (hp j hj))

end DifferentialGeometry.Geometry.Collapse
