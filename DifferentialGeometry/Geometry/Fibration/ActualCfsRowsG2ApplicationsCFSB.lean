import DifferentialGeometry.Geometry.Fibration.ActualCfs25RowCFSB
import DifferentialGeometry.Geometry.Fibration.ActualStageChainE

/-!
# Consumers of CFS22, CFS23 and CFS25 on the enhanced chain

* `Gaf02ChainE.cfs22_cfs23_CFSB`: on the chain of the PRODUCER `gaf02_chainE_row_GAF8` (final
  family `LocalChartPacketsC14`, enhanced planes), the edge and slim cutoffs are one on the
  threshold-`6` unions at `g₁`, `g₂`, with the same uniform derivative bound `C/ρ` along the
  segments, and the (ZM) inputs are the chain's own.
* `Gaf02ChainE.cfs25_CFSB`: the stage maps `Ψ₂`, `Ψ₃` of the enhanced chain are smooth on open
  neighbourhoods of the actual preceding images.
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

namespace Gaf02ChainE

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X]
  [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- CFS22 / CFS23 on the enhanced chain: the slim cutoff is one at `g₂` of the threshold-`6·10⁵Δ`
slim union and the edge cutoff is one at `g₁` of the threshold-`6Δ` edge union. -/
theorem cfs22_cfs23_CFSB (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    (∀ p, (∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) →
      gafStageThreeCutoff P.toLocalChartFamily P.zero (C.toChain.g₂ p) = 1) ∧
    ∀ p, (∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ) →
      gafStageTwoCutoff P.toLocalChartFamily P.zero (C.toChain.g₁ p) = 1 :=
  ⟨C.toChain.cfs22_row_CFSB.2.2.2.2.2.2.2.2.2.1, C.toChain.cfs23_row_CFSB.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- CFS25 on the enhanced chain: CFS18's smooth neighbourhoods of the preceding images. -/
theorem cfs25_CFSB (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    (∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen W ∧
      range C.toChain.g₁ ⊆ W ∧ ContDiffOn ℝ ∞ C.toChain.Ψ₂ W) ∧
    ∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen W ∧
      range C.toChain.g₂ ⊆ W ∧ ContDiffOn ℝ ∞ C.toChain.Ψ₃ W := by
  obtain ⟨⟨W₂, hW₂, hK₂, -, hs₂⟩, h3, -⟩ := C.toChain.cfs25_smooth_CFSB
  exact ⟨⟨W₂, hW₂, hK₂, hs₂⟩, h3⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
