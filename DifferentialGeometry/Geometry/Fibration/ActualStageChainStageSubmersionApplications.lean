import DifferentialGeometry.Geometry.Fibration.ActualStageChainStageSubmersion

/-!
# Consumers of the stage submersions

* `Gaf02Chain.stage_submersion_circle_range_BAS`: at a circle-plateau point the derivative of
  `κ_j ∘ f₁` has full range.
* `Gaf02Chain.stage_submersion_edge_range_BAS`: the same at an edge-plateau point.
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

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- At a circle-plateau point, `D(κ_j ∘ f₁)(p)` has full range. -/
theorem stage_submersion_circle_range_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (200 * ρ j.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6) :
    LinearMap.range (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun q =>
      ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (C.stageMap_BAS 0 q)) p).toLinearMap =
        ⊤ :=
  LinearMap.range_eq_top.mpr (C.stage_submersion_circle_BAS R j hp hη)

/-- At an edge-plateau point, `D(κ_j ∘ f₂)(p)` has full range. -/
theorem stage_submersion_edge_range_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (100 * Δ * ρ j.1)) (hη : |P.edge.coord j.1 p| < 6 * Δ)
    (ht : cgpHeight P.toLocalChartFamily p < 6 * Δ) :
    LinearMap.range (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (C.stageMap_BAS 1 q)) p).toLinearMap = ⊤ :=
  LinearMap.range_eq_top.mpr (C.stage_submersion_edge_BAS R j hp hη ht)

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
