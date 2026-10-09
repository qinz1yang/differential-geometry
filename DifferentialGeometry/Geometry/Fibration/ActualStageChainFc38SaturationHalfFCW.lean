import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38SaturationFCW

/-!
# FDC03: saturation of the remainder with ONE half of EDP05's relative-interior characterization

Lane S-FC-WRAP2, group G6b (suffix `_FCW`; a strengthening of `fdc03_saturation_FCW` of group G6,
which is left untouched). Blueprint `master207B.tex`, FDC03 (B:7285–7365): "for a point of
`M^edge` the relative interior in (Last) is characterized by `T < 4Δ`" (EDP05's charts). Of the two
inclusions of `int_{M₂} A = M₂ ∩ X₂°` only ONE needs the charts:

* (free) `M₂ ∩ X₂° ⊆ int_{M₂} A`: `X₂°` is OPEN (`isOpen_edgeCandidate_FDC`) and `M₂ ∩ X₂° ⊆ A`;
* (EDP05) `int_{M₂} A ⊆ X₂°`: a relative interior point of the edge piece has `T < 4Δ` (and a
  witnessing index) — at `T = 4Δ` the edge piece is not a neighbourhood in `M₂` (the vertical
  face; at a meeting with a horizontal face: the independence of `d(b ∘ f₂)` and `dT`).

`Gaf02ChainEJA.fdc03_saturation_half_FCW`: for ZSP04's `K₃` and the actual pieces, from the
explicit (hint') `int_{M₂} A ⊆ X₂°` and (hsat) EDP06's saturation of `M₂ ∩ X₁`:
`M₃ = (π₁E)⁻¹(C₁) ∩ X₁`, `C₁ = π₁E(M₃) ⊆ B₁`.
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

/-- **FDC03's saturation of the remainder with the half-characterization** (see the module
docstring). -/
theorem fdc03_saturation_half_FCW {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
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
        M₃ = (fun x => (gafStageQ P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E x)) ⁻¹'
          ((fun x => (gafStageQ P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E x)) '' M₃) ∩
          {x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E x) ∈
            Ĉ.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets} ∧
        (fun x => (gafStageQ P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E x)) '' M₃ ⊆
          Ĉ.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets := by
  obtain ⟨K₃, hKs, hall⟩ := Ĉ.fdc03_saturation_FCW hεr hσc hγ hγ1
  refine ⟨K₃, hKs, fun Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ hint hsat => ?_⟩
  refine hall Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ (Set.Subset.antisymm (fun x hx => ?_)
    (fun x hx => ?_)) hsat
  · obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q.2, hint ⟨q, hq, rfl⟩⟩
  · rw [DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff]
    refine ⟨hx.1, _, Ĉ.toGaf02ChainE.isOpen_edgeCandidate_FDC, hx.2, ?_⟩
    rintro y ⟨hy, hyM⟩
    rw [hA]
    exact ⟨⟨hyM, Or.inr ⟨(Ĉ.toChain.scale_pos y).2, le_of_lt hy.1⟩⟩, hy.2⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
