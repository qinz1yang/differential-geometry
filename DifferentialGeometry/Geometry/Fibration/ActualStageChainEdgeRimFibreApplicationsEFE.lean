import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimFibreEFE

/-!
# Consumer of EDP06's circle agreement (G5a): the final closed family

Lane S-EDP-FDC2, group G5. `edp06_rim_eq_whole_fibre_C14Z_EFE`: on the final closed family
`LocalChartPacketsC14Z`, for every enhanced chain with (JA), the boundary circle of the whole
edge disk through a point `q₀` of the actual `X₂` with `T q₀ = 4Δ` in `X₁` is exactly the whole
circle fibre of `E` through `q₀` (`edp06_rim_eq_whole_fibre_EFE`), and that fibre is a smooth
embedded circle (`circleFibre_circle_EFE`). The hypothesis `q₀ ∈ X₁` is the conclusion of EDP06's
first clause (`eventually_edp06_rim_mem_X₁_C14Z_EFC`, lane S-EDP-FDC's predecessor G7).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02ChainEJA

/-- **EDP06's circle agreement on the final closed family.** -/
theorem edp06_rim_eq_whole_fibre_C14Z_EFE {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (PZ : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) :
    type_of% (C.edp06_rim_eq_whole_fibre_EFE hβ hd) :=
  C.edp06_rim_eq_whole_fibre_EFE hβ hd

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
