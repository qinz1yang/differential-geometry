import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38SaturationGivenFCW
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38RemainderFCW
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimEFE

/-!
# FC38: saturation with (hsat) from EDP06, and compactness, for the given `K₃, D₃`

Lane S-FC-WRAP4, group G13 (suffix `_FCW`). Blueprint `master207B.tex`, FDC03 (B:7285–7365) and
EDP06 (B:7092–7133).

* `Gaf02ChainEJA.fdc03_saturation_final_FCW`: `fdc03_saturation_given_FCW` (G12) with its last
  hypothesis (hsat) PROVED from `edp06_saturation_EFE` (a point of `X₁ = (π₁E)⁻¹(W₁ ∩ R₁)` on a
  circle fibre meeting `M₂` lies in `M₂`; `X₁ ⊆ circleDomain_EFE`, `mem_circleDomain_of_EFE`;
  the stage-0 projection is the identity, so the fibres of `circleProj_EFE` are the
  `π₁E`-fibres): for ZSP04's given `K₃, D₃`, `M₃ = (π₁E)⁻¹(C₁) ∩ X₁`, `C₁ = π₁E(M₃) ⊆ B₁`, with
  only the register numerics and the five ZSP04 properties as hypotheses.
* `Gaf02ChainEJA.fdc03_remainder_compact_given_FCW`: compactness of `M₂`, `M₃` and the set-level
  (Last) for the SAME given `K₃, D₃` (`fdc03_remainder_compact_FCW` of group G6 produced its own
  `K₃`).

READING (review 77, R13 / D77-3): everything is in the full-norm system of EDP02; no claim is
made for an axis-coordinate reading.
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

/-- **FDC03's saturation of the remainder for the given `K₃, D₃`, (hsat) from EDP06** (see the
module docstring). -/
theorem fdc03_saturation_final_FCW {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A4 : SmoothStageBasesOn74 Ĉ.toChain) (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ)
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
  intro Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃
  have hM₂c : M₂ = Ĉ.toGaf02ChainE.cutM2_R74 K₃.carrier := by
    rw [hM₂, hM₁, hZ]
    rfl
  refine Ĉ.fdc03_saturation_given_FCW A4 hεr hσc hγ hγ1 hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 K₃ D₃ hD
    hKs hKF hDreg hdD Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃ ?_
  intro p hp hpX p' hp'
  subst hM₂c
  have hpd : p ∈ Ĉ.circleDomain_EFE := Ĉ.mem_circleDomain_of_EFE hpX.1 hpX.2
  have hp'd : p' ∈ Ĉ.circleDomain_EFE :=
    Ĉ.mem_circleDomain_of_EFE (by rw [hp']; exact hpX.1) (by rw [hp']; exact hpX.2)
  exact Ĉ.edp06_saturation_EFE hβ hd hεr K₃ D₃ hD hKs hKF hDreg hdD ⟨p, hpd⟩ ⟨p', hp'd⟩
    (Subtype.ext (Subtype.ext hp')) hp

/-- **Compactness of the remainder and the set-level (Last) for the given `K₃, D₃`** (see the
module docstring). -/
theorem fdc03_remainder_compact_given_FCW {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2)
    (K₃ D₃ : SmoothCompactOneDomain_BCF Ĉ.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ Ĉ.slimC3_ZSP35)
    (hKs : Ĉ.toChain.slimSlabImage_ZSP35 ∪ Ĉ.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35))
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set Ĉ.slimBs_ZSP35))) :
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
  obtain ⟨-, -, -, -, -, -, h05⟩ := Ĉ.slimPiece_spec_ZSP35 hεr K₃.isCompact_carrier_BCF
    K₃.subset_base (subset_union_right.trans hKs) (by rw [← hD]; exact hDreg)
  intro Z M₁ M₂ A M₃ hZ hM₁ hM₂ hA hM₃
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
