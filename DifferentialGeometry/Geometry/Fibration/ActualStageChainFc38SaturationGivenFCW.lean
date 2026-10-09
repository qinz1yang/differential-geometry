import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38SaturationHalfFCW
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCornerExitFCW
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeInteriorApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRemainderCircleApplications

/-!
# FDC03 on ZSP04's GIVEN `K₃, D₃`: EDP05's relative-interior inclusion (hint') is a theorem

Lane S-FC-WRAP4, group G12 (suffix `_FCW`). Blueprint `master207B.tex`, FDC03 (B:7285–7365) and
EDP05 (B:7040–7090). `fdc03_saturation_half_FCW` (group G6b) produces its OWN `K₃`, whereas the
EDP05 / EDP06 lemmas (`edge_corner_exit_FCW`, `edp06_saturation_EFE`, the faces) are stated for a
`K₃, D₃` carrying the five properties of `zsp04_D3_ZSP35`. This module states FDC03's saturation
for such a GIVEN `K₃, D₃`:

* `Gaf02ChainEJA.fdc03_hint_given_FCW` — (hint'): `int_{M₂} A ⊆ X₂°`, where `A = M₂ ∩ V ∩ W` is
  the edge piece, `X₂° = {T < 4Δ} ∩ {∃ k, v_k(E) = R_k, |u_k(E)| < 4ΔR_k}` and `M₂ = M₁ ∖
  int_{M₁} M^slim(K₃)`. Proof: `A ⊆ {T ≤ 4Δ}` (`vertical_eq_FDC`), and the witness part of `X₂°`
  is `A`'s own. At a point `x` of `int_{M₂} A` with `T x = 4Δ`: if `x ∈ int M₂`, then
  `x ∈ int (V ∩ W)` (`mem_relInterior_iff_of_mem_interior_EFC`) and EDP04's rank excludes a local
  maximum of `T` (`height_lt_of_mem_interior_EFC`); if `x ∈ ∂M₂`, then `x` is in the edge source
  (`mem_edgeSource_EFE`) and the regular horizontal–vertical corner of EDP05
  (`edge_corner_exit_FCW`) puts points of `M₂ ⊆ A` with `T > 4Δ` in every neighbourhood of `x`.
* `Gaf02ChainEJA.fdc03_saturation_given_FCW` — the saturation `M₃ = (π₁E)⁻¹(C₁) ∩ X₁`,
  `C₁ = π₁E(M₃) ⊆ B₁` for the given `K₃, D₃`, with ONLY (hsat) (EDP06's saturation of `M₂ ∩ X₁`
  by whole circle fibres, `edp06_saturation_EFE`) as hypothesis.

READING (review 77, R13 / D77-3): everything is stated in the full-norm system of EDP02 (the sets
`X₂`, `X₂°` use the full vector norm `|u_k|`); no claim is made for an axis-coordinate reading.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

namespace Gaf02ChainEJA

/-- **EDP05's relative-interior inclusion (hint') for the given `K₃, D₃`** (see the module
docstring). -/
theorem fdc03_hint_given_FCW {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A4 : SmoothStageBasesOn74 Ĉ.toChain) (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF Ĉ.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ Ĉ.slimC3_ZSP35)
    (hKs : Ĉ.toChain.slimSlabImage_ZSP35 ∪ Ĉ.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35))
      Ĉ.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set Ĉ.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set Ĉ.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' Ĉ.slimC3_ZSP35 : Set Ĉ.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35) ∩
          Ĉ.slimFacePoints_ZSP35))
    {M₂ A : Set X} (hM₂ : M₂ = Ĉ.toGaf02ChainE.cutM2_R74 K₃.carrier)
    (hA : A = M₂ ∩ ({p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪
          {p | 0 < Ĉ.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
            P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
              (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∩
          {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
            blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) =
              ρ k.1 ∧
            ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
                P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
              4 * Δ * ρ k.1}) :
    Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) ⊆
      ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
          P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
        {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
          blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
          ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1}) := by
  subst hM₂
  intro x hx
  have hx' := hx
  rw [mem_image_interior_preimage_val_iff] at hx'
  obtain ⟨hxM, O, hO, hxO, hOA⟩ := hx'
  have hxA : x ∈ A := hOA ⟨hxO, hxM⟩
  have hA' : A = Ĉ.toGaf02ChainE.cutM2_R74 K₃.carrier ∩ (({p | P.edge.smoothing p / ρ p ≤
      7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2)
        (gafHeightVector P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero
          (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ}) ∩
      {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) =
          ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
            P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
          4 * Δ * ρ k.1}) := by
    rw [hA, Set.inter_assoc]
  rw [hA] at hxA
  obtain ⟨⟨-, hV⟩, k, hk1, hk2⟩ := hxA
  have hT : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
      P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x ≤ 4 * Δ := by
    have h := hV
    rw [Ĉ.toChain.vertical_eq_FDC] at h
    exact h
  refine ⟨?_, k, hk1, hk2⟩
  by_cases hint : x ∈ interior (Ĉ.toGaf02ChainE.cutM2_R74 K₃.carrier)
  · have h2 := hx
    rw [hA'] at h2
    have hxI := (mem_relInterior_iff_of_mem_interior_EFC hint).mp h2
    refine Ĉ.toGaf02ChainE.height_lt_of_mem_interior_EFC hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 ?_ hxI
    rintro y ⟨hyV, j, hj1, hj2⟩
    have hyT : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (Ĉ.toChain.E y)) / Ĉ.toChain.scale y ≤ 4 * Δ := by
      have h := hyV
      rw [Ĉ.toChain.vertical_eq_FDC] at h
      exact h
    exact ⟨hyT, j, lt_of_lt_of_eq (by linarith [hρ j.1]) hj1.symm,
      lt_of_lt_of_eq hj2 (congrArg (fun t => 4 * Δ * t) hj1.symm)⟩
  · rcases lt_or_eq_of_le hT with hlt | hT4
    · exact hlt
    · exfalso
      have hxF : x ∈ frontier (Ĉ.edgeM2_EFE K₃) := by
        rw [frontier]
        exact ⟨subset_closure hxM, hint⟩
      obtain ⟨-, h9, h4⟩ := Ĉ.toChain.stageTwo_mem_base_FDC k hk1 hk2 hV
      have hxs : x ∈ Ĉ.edgeSource_EFE :=
        Ĉ.toGaf02ChainE.mem_edgeSource_EFE hΔ2 ⟨k, h9, h4⟩ hT
      obtain ⟨y, hyO, hyM, hys, hyT⟩ := Ĉ.edge_corner_exit_FCW A4 hεr hΔ2 hc hϑ hε0 hε hγc hγc1
        hβc1 K₃ D₃ hD hKs hKF hDreg hdD hxF hxs hT4 (hO.mem_nhds hxO)
      have hyA := hOA ⟨hyO, hyM⟩
      rw [hA] at hyA
      obtain ⟨⟨-, hyV⟩, -⟩ := hyA
      have hTy : EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
          P.zero (Ĉ.toChain.E y)) / Ĉ.toChain.scale y ≤ 4 * Δ := by
        have h := hyV
        rw [Ĉ.toChain.vertical_eq_FDC] at h
        exact h
      exact absurd hyT (not_lt.mpr hTy)

/-- **FDC03's saturation of the remainder for ZSP04's GIVEN `K₃, D₃`** (see the module
docstring): (hint') is proved (`fdc03_hint_given_FCW`); the only hypothesis on the pieces is
(hsat), EDP06's saturation of `M₂ ∩ X₁` by whole circle fibres of `π₁E`. -/
theorem fdc03_saturation_given_FCW {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A4 : SmoothStageBasesOn74 Ĉ.toChain) (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ)
    (hγ1 : γ ≤ 3 / 4) (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF Ĉ.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ Ĉ.slimC3_ZSP35)
    (hKs : Ĉ.toChain.slimSlabImage_ZSP35 ∪ Ĉ.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35))
      Ĉ.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set Ĉ.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set Ĉ.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' Ĉ.slimC3_ZSP35 : Set Ĉ.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35) ∩
          Ĉ.slimFacePoints_ZSP35)) :
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
  intro Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ hsat
  have hSeq : Ĉ.slimPiece_ZSP35 K₃.carrier =
      (interior Ĉ.zeroUnion_ZSP35)ᶜ ∩ Ĉ.slimMap_ZSP35 ⁻¹' K₃.carrier :=
    (Ĉ.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg).2.1
  have hM₂c : M₂ = Ĉ.toGaf02ChainE.cutM2_R74 K₃.carrier := by
    rw [hM₂, hM₁, hZ]
    rfl
  have hX₁ : M₃ ⊆ {x | (gafStageQ P.toLocalChartPackets.toLocalChartFamily
        P.toLocalChartPackets.zero 0).starProjection (Ĉ.toChain.E x) ∈
      Ĉ.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets} := by
    have hM₂₁ : M₂ ⊆ (interior Ĉ.zeroUnion_ZSP35)ᶜ := by
      intro x hx
      rw [hM₂, hM₁, hZ] at hx
      exact hx.1
    have hzero : ∀ x ∈ M₂, x ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0 :=
      fun x hx => Ĉ.toGaf02ChainE.not_zero_of_mem_M1_EFC hεr (hM₂₁ hx)
    have hS : ∀ x ∈ M₂, ∀ k (hk : k ∈ P.slim.centres), dist x k < 9 * Δ * ρ k →
        10 * Δ ≤ |(P.slim.centre k hk).coord x| := by
      subst hZ hM₁ hM₂
      exact fun q hq k hk hd => Ĉ.toGaf02ChainE.slim_far_of_relint_EFC
        (fun w hw => hKs (Or.inl hw)) (M₁ := (interior Ĉ.zeroUnion_ZSP35)ᶜ)
        (fun p hp hpK => by rw [hSeq]; exact ⟨hp, hpK⟩) hq hk hd
    have hAx : M₂ ∩ ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
          P.toLocalChartPackets.toLocalChartFamily P.toLocalChartPackets.zero (Ĉ.toChain.E x)) /
          Ĉ.toChain.scale x < 4 * Δ} ∩
        {x | ∃ k : P.toLocalChartPackets.edge.finite_centres.toFinset,
          blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x) =
            ρ k.1 ∧
          ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartPackets.toLocalChartFamily
              P.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ <
            4 * Δ * ρ k.1}) ⊆ A := by
      rintro x ⟨hxM, hxT, hxk⟩
      rw [hA]
      exact ⟨⟨hxM, Or.inr ⟨(Ĉ.toChain.scale_pos x).2, le_of_lt hxT⟩⟩, hxk⟩
    rw [hM₃]
    exact Ĉ.remainder_subset_X₁_EFC hσc hγ hγ1 hzero hS hAx
  have hint' := Ĉ.fdc03_hint_given_FCW A4 hεr hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
    hDreg hdD hM₂c hA
  have hint : Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) =
      M₂ ∩ ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
          P.zero (Ĉ.toChain.E x)) / Ĉ.toChain.scale x < 4 * Δ} ∩
        {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
          blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inr (.inr (.inl k))) (Ĉ.toChain.E x) = ρ k.1 ∧
          ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inr (.inr (.inl k))) (Ĉ.toChain.E x)‖ < 4 * Δ * ρ k.1}) := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨q.2, hint' ⟨q, hq, rfl⟩⟩
    · rw [DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff]
      refine ⟨hx.1, _, Ĉ.toGaf02ChainE.isOpen_edgeCandidate_FDC, hx.2, ?_⟩
      rintro y ⟨hy, hyM⟩
      rw [hA]
      exact ⟨⟨hyM, Or.inr ⟨(Ĉ.toChain.scale_pos y).2, le_of_lt hy.1⟩⟩, hy.2⟩
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
