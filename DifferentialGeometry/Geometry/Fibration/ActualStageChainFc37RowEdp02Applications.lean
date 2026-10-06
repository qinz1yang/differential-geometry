import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc37RowEdp02
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc37RowApplications

/-!
# Consumer of FC37 with EDP02's row: the height bound of `X₂` is read off, not assumed

Lane S-FC-WRAP, group G3b (suffix `_FCW`). `fc37_disk_over_image_FCW` needs `T(q) ≤ 4Δ` for the
point `q ∈ X₂`; EDP02's clause (6) (`X₂ = (π₂E)⁻¹(B₂) ∩ {T ≤ 4Δ}`) in `fc37_row_edp02_FCW` gives it.
So every point of `X₂` lies on a whole smooth embedded closed disk with rim `{T = 4Δ}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **Consumer of FC37 with EDP02's row**: every point of `X₂` lies on the whole disk fibre of
`π₂E`, a smooth embedded closed disk (no height hypothesis: `T ≤ 4Δ` on `X₂` is EDP02's (6)). -/
theorem fc37_disk_of_mem_X2_FCW
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) {q : X} (hq : q ∈ C.toGaf02ChainE.edgeTotal_EDP23) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧ q ∈ range φ ∧
      range φ = {x | (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.toChain.E x) = (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (C.toChain.E q) ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
              P.toLocalChartFamily P.zero (C.toChain.E x)) / C.toChain.scale x ≤ 4 * Δ} := by
  obtain ⟨hedp, -⟩ := C.fc37_row_edp02_FCW hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1
  obtain ⟨-, -, -, -, -, hsub, -⟩ := hedp
  have hq' := hq
  rw [hsub] at hq'
  exact C.fc37_disk_over_image_FCW hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 hq hq'.2

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
