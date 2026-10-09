import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38SaturationFCW
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CompactEdgePiece

/-!
# FDC03: compactness of the remainder and the set-level (Last) / (LastFaces)

Lane S-FC-WRAP2, group G6 (suffix `_FCW`). Blueprint `master207B.tex`, FDC03 (B:7285–7365):
"Compactness of `M₃` follows from (Last)" and `M₂ = M^edge ∪ M₃`, `M^edge ∩ M₃` the relative
frontier of `M^edge` in `M₂` (the identification of this frontier with `V_e` needs EDP05's charts
and is NOT here).

`Gaf02ChainEJA.fdc03_remainder_compact_FCW` (final family): for ZSP04's `K₃` and the actual `Z`,
`M₁`, `M₂`, edge piece `A`, `M₃ = M₂ ∖ int_{M₂} A`: `M₂` and `M₃` are compact, and, if the edge
piece `A` is compact (FDC02's compactness, the output of FC37), `M₂ = A ∪ M₃` and
`A ∩ M₃ = frontier_{M₂} A`.
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

/-- **Compactness of the remainder and the set-level (Last) / (LastFaces)** (see the module
docstring). -/
theorem fdc03_remainder_compact_FCW {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
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
        IsCompact M₂ ∧ IsCompact M₃ ∧
          (IsCompact A → M₂ = A ∪ M₃ ∧
            A ∩ M₃ = Subtype.val '' frontier (Subtype.val ⁻¹' A : Set M₂)) := by
  obtain ⟨K₃, hKs, hKF, -, hKreg, -, hSc, hreg, -⟩ := Ĉ.zsp04_row_ZSP35 hεr
  obtain ⟨-, -, -, -, -, -, h05⟩ := Ĉ.slimPiece_spec_ZSP35 hεr K₃.isCompact_carrier_BCF
    K₃.subset_base (subset_union_right.trans hKs) hKreg
  refine ⟨K₃, fun w hw => hKs (Or.inl hw), fun Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ => ?_⟩
  have hc₂ : IsCompact M₂ := by
    subst hZ hM₁ hM₂
    exact h05.1
  have : CompactSpace M₂ := isCompact_iff_compactSpace.mp hc₂
  have hAM : A ⊆ M₂ := by
    rw [hA]
    exact fun x hx => hx.1.1
  have hM₃T : M₃ = Subtype.val '' (interior (Subtype.val ⁻¹' A : Set M₂))ᶜ := by
    ext p
    constructor
    · intro hp
      rw [hM₃] at hp
      exact ⟨⟨p, hp.1⟩, fun h => hp.2 ⟨_, h, rfl⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      rw [hM₃]
      refine ⟨q.2, ?_⟩
      rintro ⟨q', hq', hqq⟩
      exact hq (Subtype.ext hqq ▸ hq')
  have hc₃ : IsCompact M₃ := by
    rw [hM₃T]
    exact (isOpen_interior.isClosed_compl.isCompact).image continuous_subtype_val
  refine ⟨hc₂, hc₃, fun hAc => ?_⟩
  obtain ⟨hU, hF, -⟩ := EdgeDisk.relativeRemoval_union_inter
    (hAc.isClosed.preimage continuous_subtype_val : IsClosed (Subtype.val ⁻¹' A : Set M₂))
  constructor
  · ext p
    constructor
    · intro hp
      have hq : (⟨p, hp⟩ : M₂) ∈ (Subtype.val ⁻¹' A : Set M₂) ∪
          (interior (Subtype.val ⁻¹' A : Set M₂))ᶜ := by rw [hU]; trivial
      rcases hq with hq | hq
      · exact Or.inl hq
      · exact Or.inr (hM₃T ▸ ⟨_, hq, rfl⟩)
    · rintro (hp | hp)
      · exact hAM hp
      · rw [hM₃] at hp
        exact hp.1
  · ext p
    constructor
    · rintro ⟨hpA, hp3⟩
      have hp3' := hp3
      rw [hM₃T] at hp3'
      obtain ⟨q, hq, rfl⟩ := hp3'
      exact ⟨q, by rw [← hF]; exact ⟨hpA, hq⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      rw [← hF] at hq
      exact ⟨hq.1, hM₃T ▸ ⟨q, hq.2, rfl⟩⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
