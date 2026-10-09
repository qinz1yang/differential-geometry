import DifferentialGeometry.Geometry.Fibration.ActualStageChainCircleCover
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBase

/-!
# Consumer: FDC03's remainder cover on the final closed family

Blueprint `master207B.tex`, FDC03 (B:7322–7335), for `Ĉ : Gaf02ChainEJA` on the final closed family
`LocalChartPacketsC14Z` (projection `P.toLocalChartPacketsC14D.toLocalChartPacketsC14`).

* `fdc03_cover_C14Z_FDC` (`σc ≤ 1/2`, `0 ≤ γ ≤ 3/4`): every point outside the interior of the edge
  candidate `X₂°` is zero-stratum, in a selected slim ball `B(j, 2Δρ_j)`, or in
  `X₁ = (π₁E)⁻¹(W₁ ∩ R₁)`; and every point of `X₂°` lies in `X₂` (`π₂E(x) ∈ W₂` with a witnessing
  edge index, `Gaf02Chain.stageTwo_mem_base_FDC`). Hence a point of `M₂` outside
  `int_{M₂}(M₂ ∩ X₂)` — a point of `M₃` — is zero-stratum, slim, or in `X₁`.
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **FDC03's remainder cover on the final closed family**: for `Ĉ : Gaf02ChainEJA`, every point
outside `int X₂°` is zero-stratum, in a slim ball `B(j, 2Δρ_j)`, or in `X₁ = (π₁E)⁻¹(W₁ ∩ R₁)`, and
`X₂° ⊆ X₂`. -/
theorem fdc03_cover_C14Z_FDC {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    (∀ x ∉ interior ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1}),
      x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0 ∨
        (∃ j ∈ P.slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
        (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (Ĉ.toChain.E x) ∈
          Ĉ.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets) ∧
    ∀ x ∈ {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1},
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E x) ∈
        Ĉ.toChain.finalBase_BAS 1 ∧
      ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        9 / 10 * ρ k.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (Ĉ.toChain.E x)) ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (Ĉ.toChain.E x))‖ <
          4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inr (.inr (.inl k))) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
              (Ĉ.toChain.E x)) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases Ĉ.fdc03_cover_FDC hσc hγ hγ1 x with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h hx
  · have hT := hx.1
    have hk := hx.2
    obtain ⟨k, hv, hu⟩ := hk
    have hV : x ∈ {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ} :=
      Or.inr ⟨(Ĉ.toChain.scale_pos x).2, le_of_lt hT⟩
    have hb := Ĉ.toChain.stageTwo_mem_base_FDC k hv hu hV
    exact ⟨hb.1, k, hb.2.1, hb.2.2⟩

end DifferentialGeometry.Geometry.Collapse
