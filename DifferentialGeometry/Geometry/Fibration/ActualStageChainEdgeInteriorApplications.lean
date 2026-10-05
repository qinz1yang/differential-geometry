import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeInterior
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeMarkerConvention
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1Applications

/-!
# Consumers: EDP02 / FDC03 on the final closed family (interior of `X₂`, relative removal)

Blueprint `master207B.tex`, EDP02 (B:6748–6775) and FDC03 (B:7285–7365, "For a point of `M^edge`
the relative interior in (Last) is characterized by `T < 4Δ`", B:7341–7344), on
`P : LocalChartPacketsC14Z` with an enhanced chain
`Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 …` (D71: the consumer keeps the
final family and forgets to `C14` for the chain).

* `interior_edgeBase_eq_C14Z_EFC`: `int X₂ = {T < 4Δ} ∩ {∃ k, v_k(E) = R_k, |u_k(E)| < 4ΔR_k}`;
* `edgeBase_ge_eq_C14Z_EFC`: the marker conventions `> .9R` / `≥ .9R` give the same `X₂`;
* `smaller_set_interior_X2_C14Z_EFC`: EDP02's interior clause for the actual `X₂`;
* `fdc03_relative_removal_C14Z_EFC`: for the ACTUAL `M₂ = M₁ \ int_{M₁} Sl`, `M₁ = M \ int Z`
  (`Z = ⋃_k Z_k`, ZSP02's domains; any slim set `Sl`), at every point `x` of the ambient interior of
  `M₂`: `x ∈ int_{M₂}(M₂ ∩ X₂)` iff `T(x) < 4Δ` and `x` is witnessed, and `x ∈ M₃` iff it is not.
  At points of `∂M₂` (horizontal faces) the relative interior needs EDP05's face charts (R0/R1,
  review D74-14): not claimed here.

Numeric premises (parameters only, as `edge_vertical_rank_C14Z_EDPE`): `Δ ≥ 2`, `c₃ < 10⁻⁵`,
`C_ρΛΔ < 10⁻⁶`, `0 ≤ ε < 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`.
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

/-- **The ambient interior of the actual `X₂` on the final closed family** (EDP02 / FDC03). -/
theorem interior_edgeBase_eq_C14Z_EFC
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hΔ : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) :
    interior ({x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
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
          P.toLocalChartPackets.zero (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ})) =
    {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartPackets.toLocalChartFamily
        P.toLocalChartPackets.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
          4 * Δ * ρ k.1} :=
  Ĉ.interior_edgeBase_eq_EFC hΔ hc hϑ hε0 hε hγc hγc1 hβc1

/-- **EDP02's marker-convention equality on the final closed family** (`Δ ≥ 2`). -/
theorem edgeBase_ge_eq_C14Z_EFC
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hΔ : 2 ≤ Δ) :
    {x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
          P.toLocalChartPackets.zero 1).starProjection (Ĉ.toChain.E x) ∈
            Ĉ.toChain.finalBase_BAS 1 ∧
        ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
          9 / 10 * ρ k.1 ≤ blockMarkerCLM (V := fun _ : CGPTag
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
      ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartPackets.toLocalChartFamily
          P.toLocalChartPackets.zero (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) :=
  Ĉ.edgeBase_ge_eq_EFC hΔ

/-- **EDP02's interior clause on the final closed family**: `{|η_k| ≤ 3.5Δ, t ≤ 3.5Δ} ∩ U_k`
lies in the ambient interior of the actual `X₂`. -/
theorem smaller_set_interior_X2_C14Z_EFC
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (k : P.toLocalChartPackets.edge.finite_centres.toFinset) {x : X}
    (hball : x ∈ ball k.1 (100 * Δ * ρ k.1)) (hη : |P.edge.coord k.1 x| ≤ 35 / 10 * Δ)
    (ht : P.edge.smoothing x / ρ x ≤ 35 / 10 * Δ) :
    x ∈ interior ({x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
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
          P.toLocalChartPackets.zero (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ})) :=
  Ĉ.smaller_set_interior_X2_EFC k hball hη ht

/-- **FDC03's relative removal at ambient interior points of the actual `M₂`** (final closed
family): with `Z = ⋃_k Z_k` (ZSP02), `M₁ = M \ int Z`, `M₂ = M₁ \ int_{M₁} Sl` for a slim set `Sl`,
`M^edge = M₂ ∩ X₂` and `M₃ = M₂ \ int_{M₂} M^edge`: at every `x ∈ int M₂`,
`x ∈ int_{M₂} M^edge ↔ x ∈ X₂°` and `x ∈ M₃ ↔ x ∉ X₂°`, where
`X₂° = {T < 4Δ} ∩ {∃ k, v_k(E) = R_k, |u_k(E)| < 4ΔR_k}`. -/
theorem fdc03_relative_removal_C14Z_EFC
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    {Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw}
    (hΔ : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) (Sl : Set X) {x : X}
    (hx : x ∈ interior ((interior (⋃ k : P.zero.finite_centres.toFinset,
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' Sl : Set ((interior (⋃ k : P.zero.finite_centres.toFinset,
            zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ : Set X)))) :
    (x ∈ Subtype.val '' interior (Subtype.val ⁻¹' (((interior (⋃ k : P.zero.finite_centres.toFinset,
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' Sl : Set ((interior (⋃ k : P.zero.finite_centres.toFinset,
            zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ : Set X))) ∩
        ({x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
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
          P.toLocalChartPackets.zero (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ})))
        : Set ((interior (⋃ k : P.zero.finite_centres.toFinset,
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' Sl : Set ((interior (⋃ k : P.zero.finite_centres.toFinset,
            zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ : Set X)) : Set X)) ↔
      x ∈ {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
          P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero (Ĉ.toChain.E x)) /
          Ĉ.toChain.scale x < 4 * Δ} ∩
        {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
          blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
          ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
            4 * Δ * ρ k.1}) := by
  rw [mem_relInterior_iff_of_mem_interior_EFC hx,
    Ĉ.interior_edgeBase_eq_EFC hΔ hc hϑ hε0 hε hγc hγc1 hβc1]

end DifferentialGeometry.Geometry.Collapse
