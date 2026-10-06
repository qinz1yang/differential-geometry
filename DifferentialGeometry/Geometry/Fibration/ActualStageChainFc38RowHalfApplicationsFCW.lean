import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38RowHalfFCW
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimFibreEFE

/-!
# Consumer of the FC38 row candidate v3 (G6b): whole circles through the remainder

Lane S-FC-WRAP2, group G6b. `fc38_saturated_circle_half_FCW`: on the final family, for ZSP04's `K₃`
and the actual pieces, under the two explicit hypotheses of `fdc03_saturation_half_FCW` (EDP05's
converse inclusion `int_{M₂} A ⊆ X₂°`, EDP06's saturation), every point of the remainder
`M₃ = M^{2-stratum}` lies on a smooth embedded circle (a WHOLE fibre of `π₁E`, GAF07 /
`circleFibre_circle_EFE`) that is contained in `M₃` (the saturation of FDC03).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.Endpoint

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
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

namespace Gaf02ChainEJA

/-- **Whole circles through the remainder** (see the module docstring). -/
theorem fc38_saturated_circle_half_FCW {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF Ĉ.slimBs_ZSP35,
      Ĉ.toChain.slimSlabImage_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35) ∧
      ∀ (Z M₁ M₂ A M₃ : Set X),
        Z = ⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E → M₁ = (interior Z)ᶜ →
        M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' Ĉ.slimPiece_ZSP35 K₃.carrier :
          Set M₁) →
        A = M₂ ∩ ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪
          {p | 0 < Ĉ.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
            P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
              (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∩
          {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
            blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) =
              ρ k.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
              4 * Δ * ρ k.1} →
        M₃ = M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) →
        Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) ⊆
          ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
              P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
            {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
              blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1}) →
        (∀ p ∈ M₂, (gafStageQ P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E p) ∈
          Ĉ.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets →
          ∀ p', (gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E p') =
            (gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E p) → p' ∈ M₂) →
        ∀ p ∈ M₃, ∃ f : Circle → X, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧ p ∈ range f ∧
          range f ⊆ M₃ := by
  obtain ⟨K₃, hKs, hall⟩ := Ĉ.fdc03_saturation_half_FCW hεr hσc hγ hγ1
  refine ⟨K₃, hKs, fun Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ hint hsat p hp => ?_⟩
  obtain ⟨hsd, hCB⟩ := hall Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ hint hsat
  have hpB : (gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero 0
      ).starProjection (Ĉ.toChain.E p) ∈ Ĉ.toChain.circleBase_BAS := by
    rw [(Ĉ.gaf07_circle_row_GAFD hβ hd).1.1]
    exact hCB ⟨p, hp, rfl⟩
  obtain ⟨f, hf, hrf⟩ := Ĉ.circleFibre_circle_EFE hβ hd hpB
  refine ⟨f, hf, ?_, ?_⟩
  · rw [hrf]
    rfl
  · intro y hy
    rw [hrf] at hy
    have hy' : (gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero 0
        ).starProjection (Ĉ.toChain.E y) = (gafStageQ P.toLocalChartPackets.toLocalChartFamily
          P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E p) := hy
    rw [hsd]
    refine ⟨⟨p, hp, hy'.symm⟩, ?_⟩
    change (gafStageQ P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero 0
      ).starProjection (Ĉ.toChain.E y) ∈
      Ĉ.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets
    rw [hy']
    exact hCB ⟨p, hp, rfl⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
