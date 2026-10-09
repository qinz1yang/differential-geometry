import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBCF03RestNoG6cBC3d
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPiecesHX1ConsumerBC2

/-!
# The rim inclusions of the BCF03 row as ONE explicit conjunction (lane S-BCF03e, G2)

After S-BCF03d G2 the BCF03 row and the V32 exports of A4 take, besides `hG4` and the register
block, four separate inclusions about the slim choice `Kc` only (no `er`, no labels):

* `hX1 : R_c ⊆ X₁` (now a theorem: `BoundaryCompactSlimChoiceV2.remainder_subset_source_BC2`),
* `hV : V_e ⊆ R_c`, `hF : R_c ∩ ∂M₂ ⊆ ∂M₂ ∖ int_{∂M₂} H_e`, `hsat : X₁ ∩ f₁⁻¹ (f₁ R_c) ⊆ R_c`
  (external review, draft request 81).

This module restates them as a single hypothesis `∀ Bs, WF → Z → ∀ Kc, P₁ ∧ P₂ ∧ P₃ ∧ P₄`
(explicit conjunction, no new named `Prop`) and proves that it is equivalent to the four separate
`∀`-hypotheses (`rim_conj_iff_BC3e`), so a reviewer's answer can be landed as one statement or as
four. Variants with `hX1` discharged (`...rim3...`, a conjunction of the three inclusions that
the review is about) are provided for every layer:

* `bcf02_pieces_of_rim_BC3e`, `bcf02_pieces_of_rim3_BC3e`: BCF02's five-conjunct `hG6` of the row;
* `bcf03_face_partition_of_rim_BC3e`, `bcf03_face_partition_of_rim3_BC3e`: the BCF03 row for fixed
  `Kc`, `er`;
* `exists_boundaryGeometricExports74V32_A4_rim_BC3e`, `..._rim3_BC3e`: the V32 exports with A4
  produced; the non-register inputs are `hG4` and ONE conjunction (four resp. three conjuncts).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

section Kc

variable {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

namespace BoundaryCompactSlimChoiceV2

/-- **`hG6` from one conjunction of the four inclusions** (`bcf02_pieces_of_rest_BC2` with the
four inclusions bundled). -/
theorem bcf02_pieces_of_rim_BC3e (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hrim : Kc.remainder ⊆ Bs.source 0 ∧ Kc.verticalFace ⊆ Kc.remainder ∧
      Kc.remainder ∩ frontier Kc.M₂ ⊆
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Bs.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' Kc.remainder) ⊆ Kc.remainder) :
    Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder = Bs.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.stageMap 1 p) = 0 :=
  Kc.bcf02_pieces_of_rest_BC2 er hrim.1 hrim.2.1 hrim.2.2.1 hrim.2.2.2

/-- **`hG6` from one conjunction of the three inclusions `hV`, `hF`, `hsat`** (`hX1` is
`remainder_subset_source_BC2`; its register premises are the explicit arguments). -/
theorem bcf02_pieces_of_rim3_BC3e (Z : BoundaryActualZeroDomains_BIFc C Bs)
    (Kc : BoundaryCompactSlimChoiceV2 Bs) (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) (hγ34 : γ ≤ 3 / 4) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hrim : Kc.verticalFace ⊆ Kc.remainder ∧
      Kc.remainder ∩ frontier Kc.M₂ ⊆
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Bs.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' Kc.remainder) ⊆ Kc.remainder) :
    Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder = Bs.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.stageMap 1 p) = 0 :=
  Kc.bcf02_pieces_of_rim_BC3e er
    ⟨Kc.remainder_subset_source_BC2 Z hΔ hΛ hμ hσc hσs hσs1 hγ34 hLΛ, hrim⟩

end BoundaryCompactSlimChoiceV2

end Kc

namespace BoundaryGaf02ChainE

section Iff

variable {C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj}

/-- **One conjunction versus four hypotheses**: the four rim / circle-fibre inclusions
quantified over every v2b decomposition, as one `∀ …, P₁ ∧ P₂ ∧ P₃ ∧ P₄` or as four `∀ …, Pᵢ`. -/
theorem rim_conj_iff_BC3e :
    (∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.remainder ⊆ Bs.source 0 ∧ Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder) ↔
    ((∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.remainder ⊆ Bs.source 0) ∧
    (∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder) ∧
    (∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.remainder ∩ frontier Kc.M₂ ⊆
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace) ∧
    (∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
        Kc.remainder)) :=
  ⟨fun h => ⟨fun Bs WF Z Kc => (h Bs WF Z Kc).1, fun Bs WF Z Kc => (h Bs WF Z Kc).2.1,
      fun Bs WF Z Kc => (h Bs WF Z Kc).2.2.1, fun Bs WF Z Kc => (h Bs WF Z Kc).2.2.2⟩,
    fun h Bs WF Z Kc => ⟨h.1 Bs WF Z Kc, h.2.1 Bs WF Z Kc, h.2.2.1 Bs WF Z Kc,
      h.2.2.2 Bs WF Z Kc⟩⟩

/-- **One conjunction versus three hypotheses** (`hV`, `hF`, `hsat`; `hX1` is a theorem). -/
theorem rim3_conj_iff_BC3e :
    (∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder) ↔
    ((∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder) ∧
    (∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.remainder ∩ frontier Kc.M₂ ⊆
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace) ∧
    (∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
        Kc.remainder)) :=
  ⟨fun h => ⟨fun Bs WF Z Kc => (h Bs WF Z Kc).1, fun Bs WF Z Kc => (h Bs WF Z Kc).2.1,
      fun Bs WF Z Kc => (h Bs WF Z Kc).2.2⟩,
    fun h Bs WF Z Kc => ⟨h.1 Bs WF Z Kc, h.2.1 Bs WF Z Kc, h.2.2 Bs WF Z Kc⟩⟩

end Iff

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCF03 G7 from ONE conjunction of the four inclusions** (consumer of
`bcf03_face_partition_of_rest_noG6c_BC3d`). -/
theorem bcf03_face_partition_of_rim_BC3e {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (h3βc : 3 * βc ≤ β 2) (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hrim : Kc.remainder ⊆ Bs.source 0 ∧ Kc.verticalFace ⊆ Kc.remainder ∧
      Kc.remainder ∩ frontier Kc.M₂ ⊆
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
        Kc.remainder) :
    (∀ x ∈ frontier Kc.M₂, ∃ P : Surface.EmbeddedFacePartition_BCF
        (connectedComponentIn (frontier Kc.M₂) x),
      (∀ i, ∃ y ∈ C.toChain.stageMap 1 '' Kc.horizontalFace,
        Subtype.val '' P.disk i = connectedComponentIn (frontier Kc.M₂) x ∩ Bs.fibre 1 y) ∧
      Subtype.val '' (⋃ j, P.piece j) = connectedComponentIn (frontier Kc.M₂) x ∩ Kc.remainder) ∧
    ∀ i : Fin S.packet.cusp.count,
      (∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y ∧
        C.toChain.cuspFront_BIF i ⊆ Kc.piece) ∨
        (∃ x ∈ Kc.remainder, C.toChain.cuspFront_BIF i =
            connectedComponentIn (frontier Kc.remainder) x ∧
          Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) :=
  C.bcf03_face_partition_of_rest_noG6c_BC3d WF Z hrd hrd4 hrdc hprem hθ Kc er hΔ hΛ hμ hτ hσc hn
    hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ h3βc hγ hγ34 hC hrim.1 hrim.2.1 hrim.2.2.1
    hrim.2.2.2

/-- **BCF03 G7 from ONE conjunction of the three inclusions `hV`, `hF`, `hsat`** (`hX1` by
`remainder_subset_source_BC2`; consumer of `bcf03_face_partition_of_rim_BC3e`). -/
theorem bcf03_face_partition_of_rim3_BC3e {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (h3βc : 3 * βc ≤ β 2) (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hrim : Kc.verticalFace ⊆ Kc.remainder ∧
      Kc.remainder ∩ frontier Kc.M₂ ⊆
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
        Kc.remainder) :
    (∀ x ∈ frontier Kc.M₂, ∃ P : Surface.EmbeddedFacePartition_BCF
        (connectedComponentIn (frontier Kc.M₂) x),
      (∀ i, ∃ y ∈ C.toChain.stageMap 1 '' Kc.horizontalFace,
        Subtype.val '' P.disk i = connectedComponentIn (frontier Kc.M₂) x ∩ Bs.fibre 1 y) ∧
      Subtype.val '' (⋃ j, P.piece j) = connectedComponentIn (frontier Kc.M₂) x ∩ Kc.remainder) ∧
    ∀ i : Fin S.packet.cusp.count,
      (∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y ∧
        C.toChain.cuspFront_BIF i ⊆ Kc.piece) ∨
        (∃ x ∈ Kc.remainder, C.toChain.cuspFront_BIF i =
            connectedComponentIn (frontier Kc.remainder) x ∧
          Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) :=
  C.bcf03_face_partition_of_rim_BC3e WF Z hrd hrd4 hrdc hprem hθ Kc er hΔ hΛ hμ hτ hσc hn hT hσs
    hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ h3βc hγ hγ34 hC
    ⟨Kc.remainder_subset_source_BC2 Z (by linarith) hΛ hμ hσc hσs hσs1 hγ34 hLΛ, hrim⟩

/-- **The V32 exports with A4 produced, from `hG4` and ONE conjunction of the four inclusions**
(consumer of `exists_boundaryGeometricExports74V32_A4_rest_BC3d`). -/
theorem exists_boundaryGeometricExports74V32_A4_rim_BC3e
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K)
    (hn : 32 * (1000000 * Δ) ≤ (n : ℝ)) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hbA : b ≤ 1 / (1000 * Δ))
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (h3βc : 3 * βc ≤ β 2) (hγ0 : 0 ≤ γ)
    (hG4 : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      ∃ er : BoundaryRelativeEdgeRestrictionV2 Kc, ∀ ℓ, ∀ y ∈ Bs.base 1, er.faceFun ℓ y = 0 →
        ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
          y ∈ O ∧ ContDiffOn ℝ ∞ (er.faceFun ℓ) O)
    (hrim : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.remainder ⊆ Bs.source 0 ∧ Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74V32 C.toChain dec :=
  C.exists_boundaryGeometricExports74V32_A4_rest_BC3d hβ2 hγ hd hK hn hμ hτ hσc hbA hC hε0 hε hγc
    hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ hΔ hΛ hT hσs hσs1 hb hs hσL hbη h3b hbH hLΛ hμΔ h3βc
    hγ0 hG4 (rim_conj_iff_BC3e.1 hrim).1 (rim_conj_iff_BC3e.1 hrim).2.1
    (rim_conj_iff_BC3e.1 hrim).2.2.1 (rim_conj_iff_BC3e.1 hrim).2.2.2

/-- **The V32 exports with A4 produced, from `hG4` and ONE conjunction of the three inclusions
`hV`, `hF`, `hsat`** (`hX1` by `remainder_subset_source_BC2`; consumer of
`exists_boundaryGeometricExports74V32_A4_rim_BC3e`). -/
theorem exists_boundaryGeometricExports74V32_A4_rim3_BC3e
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K)
    (hn : 32 * (1000000 * Δ) ≤ (n : ℝ)) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hbA : b ≤ 1 / (1000 * Δ))
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (h3βc : 3 * βc ≤ β 2) (hγ0 : 0 ≤ γ)
    (hG4 : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      ∃ er : BoundaryRelativeEdgeRestrictionV2 Kc, ∀ ℓ, ∀ y ∈ Bs.base 1, er.faceFun ℓ y = 0 →
        ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
          y ∈ O ∧ ContDiffOn ℝ ∞ (er.faceFun ℓ) O)
    (hrim : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74V32 C.toChain dec :=
  C.exists_boundaryGeometricExports74V32_A4_rim_BC3e hβ2 hγ hd hK hn hμ hτ hσc hbA hC hε0 hε hγc
    hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ hΔ hΛ hT hσs hσs1 hb hs hσL hbη h3b hbH hLΛ hμΔ h3βc
    hγ0 hG4 fun Bs WF Z Kc =>
      ⟨Kc.remainder_subset_source_BC2 Z (by linarith) hΛ hμ hσc hσs hσs1 (by linarith) hLΛ,
        hrim Bs WF Z Kc⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
