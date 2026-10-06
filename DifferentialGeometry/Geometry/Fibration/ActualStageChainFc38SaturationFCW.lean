import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38Row

/-!
# FC38 / FDC03: saturation of the remainder `M₃` by whole circle fibres, from EDP06 and EDP05

Lane S-FC-WRAP2, group G6 (suffix `_FCW`). Blueprint `master207B.tex`, FDC03
(`thm:fibration-actual-circle-remainder`, B:7285–7365): `M^{2-stratum} := M₃ = E⁻¹(C₁) ∩ X₁`,
`C₁ = E(M₃) ⊆ B₁`. The blueprint's proof: EDP06 proves that `M₂ ∩ X₁` is saturated by whole circle
fibres; membership in `X₂` is constant on each fibre (the base point `π₂E` and the height `T` are
functions of `E`); for a point of `M^edge` the relative interior in (Last) is characterized by
`T < 4Δ` (EDP05's charts, including the horizontal face); hence `M₃` is saturated.

* `remainder_fibre_saturated_FCW` (kernel, any map `F`): from the relative-interior
  characterization `int_{M₂} A = M₂ ∩ X₂`, `F`-constancy of `X₂`, and the saturation of `M₂ ∩ X₁`
  by `F`-fibres, the remainder `M₃ = M₂ ∖ int_{M₂} A ⊆ X₁` equals `F⁻¹(F(M₃)) ∩ X₁`.
* `Gaf02ChainEJA.fdc03_saturation_FCW` (final family): the kernel for `F = π₁E`
  (`= E`, the stage-0 projection is the identity) and ZSP04's `K₃` and the actual `Z`, `M₁`, `M₂`,
  edge piece `A`, `M₃`; `X₂° = {T < 4Δ} ∩ {∃ k, v_k(E) = R_k, |u_k(E)| < 4ΔR_k}` and the
  `E`-fibre constancy of `X₂°` is `fdc03_remainder_C14Z_FDC`; `M₃ ⊆ X₁` is
  `fdc03_remainder_subset_X₁_C14Z_EFC`. The two EXPLICIT hypotheses are the two not yet delivered
  clauses: (hint) EDP05's relative-interior characterization and (hsat) EDP06's saturation.
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

/-- **FDC03 kernel (saturation of the remainder by `F`-fibres).** If the relative interior of `A`
in `M₂` is `M₂ ∩ X₂`, membership in `X₂` is constant on the fibres of `F`, `M₂ ∩ X₁` is a union of
`F`-fibres, and `M₃ = M₂ ∖ int_{M₂} A` lies in `X₁`, then `M₃ = F⁻¹(F(M₃)) ∩ X₁`. -/
theorem remainder_fibre_saturated_FCW {Y Z : Type*} [TopologicalSpace Y] (F : Y → Z)
    {M₂ A X₂ X₁ : Set Y}
    (hint : Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) = M₂ ∩ X₂)
    (hX₂ : ∀ p p', F p = F p' → (p ∈ X₂ ↔ p' ∈ X₂))
    (hsat : ∀ p ∈ M₂ ∩ X₁, ∀ p', F p' = F p → p' ∈ M₂)
    (hX₁ : M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) ⊆ X₁) :
    M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) =
      F ⁻¹' (F '' (M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂))) ∩ X₁ := by
  ext p'
  constructor
  · intro hp'
    exact ⟨⟨p', hp', rfl⟩, hX₁ hp'⟩
  · rintro ⟨⟨p, hp, hFp⟩, hp'X₁⟩
    have hpX₁ : p ∈ X₁ := hX₁ hp
    have hp'M₂ : p' ∈ M₂ := hsat p ⟨hp.1, hpX₁⟩ p' hFp.symm
    refine ⟨hp'M₂, fun hint' => ?_⟩
    rw [hint] at hint'
    have hpX₂ : p ∈ X₂ := (hX₂ p p' hFp).mpr hint'.2
    exact hp.2 (by rw [hint]; exact ⟨hp.1, hpX₂⟩)

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

namespace Gaf02ChainEJA

/-- **FDC03's saturation of the remainder, from EDP06 and EDP05** (see the module docstring): for
ZSP04's `K₃` and the actual pieces `Z`, `M₁`, `M₂`, `A`, `M₃`, if (hint) the relative interior of
`A` in `M₂` is `M₂ ∩ X₂°` (EDP05's charts: the relative interior of the edge piece is cut out by
`T < 4Δ`) and (hsat) `M₂ ∩ X₁` is a union of whole circle fibres of `π₁E` (EDP06), then
`M₃ = (π₁E)⁻¹(C₁) ∩ X₁` with `C₁ = π₁E(M₃) ⊆ B₁`. -/
theorem fdc03_saturation_FCW {cadj : ℝ}
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
        Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) =
          M₂ ∩ ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
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
  obtain ⟨K₃, hKs, hall⟩ := fdc03_remainder_subset_X₁_C14Z_EFC Ĉ hεr hσc hγ hγ1
  refine ⟨K₃, hKs, fun Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ hint hsat => ?_⟩
  have hX₁ := hall Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃
  have hπ0 : ∀ y, (gafStageQ P.toLocalChartPackets.toLocalChartFamily
      P.toLocalChartPackets.zero 0).starProjection y = y :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  have hfib := (fdc03_remainder_C14Z_FDC Ĉ.toGaf02ChainE hσc).2.2
  have key := remainder_fibre_saturated_FCW (fun x => (gafStageQ
      P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero 0).starProjection
      (Ĉ.toChain.E x)) (M₂ := M₂) (A := A) hint
    (X₂ := {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
              P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
            {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
              blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
              ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1})
    (X₁ := {x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E x) ∈
            Ĉ.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets})
    (fun p p' h => hfib p p' (by rwa [hπ0, hπ0] at h))
    (fun p hp p' h => hsat p hp.1 hp.2 p' h) (hM₃ ▸ hX₁)
  rw [hM₃]
  refine ⟨key, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (hM₃ ▸ hX₁) hx

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
