import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPiecesCornersBC2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBCF03RowBCF

/-!
# BCF02 pieces, part 2: `hG6` reduced to four atomic rim / circle facts (lane S-BCF02, G2b)

The five conjuncts that `bcf03_face_partition_of_rows_BCF` takes as the explicit input `hG6`
(the conjuncts 4-8 of the frozen `bcf02_pieces_BCF02`) are assembled from

* the interface-level halves of G2a (`edgePiece_inter_remainder_subset_BC2`,
  `frontier_sdiff_subset_remainder_BC2`, `corner_unique_BC2`, proved), and
* four ATOMIC geometric facts, each a plain inclusion (no new `Prop`, no structure):
  `hX1 : R_c ⊆ X₁`, `hV : V_e ⊆ R_c`, `hF : R_c ∩ ∂M₂ ⊆ ∂M₂ ∖ int_{∂M₂} H_e`,
  `hsat : X₁ ∩ f₁⁻¹(f₁(R_c)) ⊆ R_c` (whole circle fibres).

`BoundaryCompactSlimChoiceV2.bcf02_pieces_of_rest_BC2` is the assembly;
`BoundaryGaf02ChainE.bcf03_face_partition_of_rest_BC2` is its consumer: the whole BCF03 row with
`hG6` replaced by the four atomic facts (so the row's input shrinks from five conjuncts to four
inclusions, none of them about labels).
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

section Assembly

variable {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

namespace BoundaryCompactSlimChoiceV2

/-- **`hG6` from four atomic facts**: the conjuncts 4-8 of the frozen `bcf02_pieces_BCF02` follow
from `R_c ⊆ X₁`, `V_e ⊆ R_c`, `R_c ∩ ∂M₂ ⊆ ∂M₂ ∖ int H_e` and the saturation of `R_c` by whole
circle fibres, together with the interface (`corner_unique_BC2`, the two easy halves). -/
theorem bcf02_pieces_of_rest_BC2 (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hX1 : Kc.remainder ⊆ Bs.source 0)
    (hV : Kc.verticalFace ⊆ Kc.remainder)
    (hF : Kc.remainder ∩ frontier Kc.M₂ ⊆
      frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace)
    (hsat : Bs.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' Kc.remainder) ⊆ Kc.remainder) :
    Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder = Bs.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.stageMap 1 p) = 0 := by
  refine ⟨hX1, ?_, ?_, ?_, fun p hp => er.corner_unique_BC2 hp⟩
  · exact Subset.antisymm Kc.edgePiece_inter_remainder_subset_BC2
      (fun p hp => ⟨hp.1, hV hp⟩)
  · exact Subset.antisymm hF Kc.frontier_sdiff_subset_remainder_BC2
  · exact Subset.antisymm (fun x hx => ⟨hX1 hx, x, hx, rfl⟩) hsat

end BoundaryCompactSlimChoiceV2

end Assembly

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCF03 G7, the whole row with `hG6` replaced by four atomic facts** (consumer of
`bcf02_pieces_of_rest_BC2`; every other input is that of `bcf03_face_partition_of_rows_BCF`). -/
theorem bcf03_face_partition_of_rest_BC2 {Bs : BoundaryGaf02BasesV2 C.toChain}
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
    (hX1 : Kc.remainder ⊆ Bs.source 0)
    (hV : Kc.verticalFace ⊆ Kc.remainder)
    (hF : Kc.remainder ∩ frontier Kc.M₂ ⊆
      frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace)
    (hsat : Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
      Kc.remainder)
    (hG6c : CircleBaseCornersV32 Kc) :
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
  C.bcf03_face_partition_of_rows_BCF WF Z hrd hrd4 hrdc hprem hθ Kc er hΔ hΛ hμ hτ hσc hn hT hσs
    hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ h3βc hγ hγ34 hC
    (Kc.bcf02_pieces_of_rest_BC2 er hX1 hV hF hsat) hG6c

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
