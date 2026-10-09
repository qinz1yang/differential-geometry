import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeInteriorApplications

/-!
# D74-11's set equality: the actual `X₂` is a height sublevel of the base preimage

Draft 74, D74-11: "the FDC actual edge set carries a low-height branch — replacing it by the single
condition `height ≤ 4Δ` goes through EDP's actual set equality, never by dropping the branch".
Blueprint `master207B.tex`, EDP02 (B:6770–6774: "On the full preimage of `B₂`, the low branch in
(ED) implies `T < 4Δ`, so `X₂ = (π₂E)⁻¹(B₂) ∩ {T ≤ 4Δ}`. This equality is proved for the actual
base; the original union is retained in the definition"). The global equality `V = {t ≤ .35Δ} ∪ {s >
0, T ≤ 4Δ} = {T ≤ 4Δ}` is lane C14-FDCb's `Gaf02Chain.vertical_eq_FDC`; here it is applied to the
ACTUAL `X₂ = (π₂E)⁻¹(B₂) ∩ V` (`W₂ = C.finalBase_BAS 1`) on the final closed family, so that the
rows' `EdgeBundle` (`height = T = A/s`, `level = 4Δ`, `source = (π₂E)⁻¹(B₂)`) sees exactly `X₂` as
`{x ∈ source | height x ≤ level}`:

* `Gaf02ChainE.edgeBase_eq_heightSublevel_EFC` (chain form) and
  `edgeBase_eq_heightSublevel_C14Z_EFC` (final family).
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
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

namespace Gaf02ChainE

/-- **The actual `X₂` as a height sublevel** (chain form): `(π₂E)⁻¹(B₂) ∩ V =
(π₂E)⁻¹(B₂) ∩ {T ≤ 4Δ}`, the low branch of `V` being absorbed by EDP02's set equality. -/
theorem edgeBase_eq_heightSublevel_EFC
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
        Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : L.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) =
    {x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
        Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : L.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
            (.inr (.inr (.inl k)))
            ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      {p | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} := by
  rw [Ĉ.toChain.vertical_eq_FDC]

end Gaf02ChainE

/-- **D74-11's set equality on the final closed family**: the actual `X₂` (with the low branch of
`V` retained in its definition) equals the height sublevel `{T ≤ 4Δ}` of the base preimage
`(π₂E)⁻¹(B₂)`. -/
theorem edgeBase_eq_heightSublevel_C14Z_EFC
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw) :
    {x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
          P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x) ∈
            Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag
              P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
            (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
            ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
            ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartPackets.toLocalChartFamily
          P.toLocalChartPackets.zero (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) =
    {x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
          P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x) ∈
            Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag
              P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero => ℝ²)
            (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
            ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
            ((gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x))} ∩
      {p | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartPackets.toLocalChartFamily
          P.toLocalChartPackets.zero (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} :=
  Ĉ.edgeBase_eq_heightSublevel_EFC

end DifferentialGeometry.Geometry.Collapse
