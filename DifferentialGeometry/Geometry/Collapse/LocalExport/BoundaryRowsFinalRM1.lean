import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimActualRM1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBCF03RestNoG6cBC3d
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgePieceCompactBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPiecesUnconditionalBC2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersProducerG6C
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphPresentationRowsBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphPresentationProductBCFApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryMemberLabelledCertificateOBDgA01B
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryH2InstanceHB
import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterChainEReadyRNUM
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42SequenceBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphThresholdFinalRM1

/-!
# The chapter-14 boundary row statements, closed (lane S-RIM81, G7)

Four row statements of the boundary chain, each from accepted terms and the `_RM1` rim theorems
(review 81 B⁺), with only register numerics as inputs:

* `BoundaryGaf02ChainE.bcf02_pieces_final_RM1`: the frozen eight-conjunct conclusion of
  `bcf02_pieces_BCF02` together with `CircleBaseCornersV32 Kc`, over `(WF, Z, Kc, er)`, the
  eighteen register premises of the row, `γ ≤ 3/4` and the circle-base register block `rd`;
* `BoundaryGaf02ChainE.bcf03_face_partition_final_RM1`: the frozen two-conjunct
  `bcf03_face_partition_BCF03` with every atomic input produced;
* `BoundaryGaf02ChainE.boundary_rawGraphPresentation_V32_A4_RM1`: the labelled raw graph
  presentation on the same carrier (rows of the actual decomposition and
  `exists_rawGraphPresentation_of_rows_BCF04`);
* `boundary_sequence_binding_final_RM1`: the per-sequence binding (one `δ*`, one tail `N`, a
  certificate with the rim-product clause and the labelled external boundary for every late
  member), with only `K ≥ 10` and `A` positive on `(0, ω₃)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCF02 pieces, the whole row** (the frozen `bcf02_pieces_BCF02` conclusion, with `hγ34`, and
the circle-base corner model `CircleBaseCornersV32`): the eight frozen conjuncts and the V32 corners
from the register numerics and the interface objects `(WF, Z, Kc, er)` only. -/
theorem bcf02_pieces_final_RM1 {Bs : BoundaryGaf02BasesV2 C.toChain}
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
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000) (hγ34 : γ ≤ 3 / 4) :
    (IsCompact Kc.edgePiece ∧ IsCompact Kc.remainder ∧ Kc.M₂ = Kc.edgePiece ∪ Kc.remainder ∧
      Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder = Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.toChain.stageMap 1 p) = 0) ∧
      CircleBaseCornersV32 Kc := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := C.bcf02_pieces_actual_RM1 WF Z Kc er (by linarith) hΛ hμ hσc hσs
    hσs1 hγ34 hLΛ
  have hcl := Kc.isClosed_edgePiece_BCF Z hΔ hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b
    hbH hLΛ hμΔ
  exact ⟨⟨Kc.isCompact_edgePiece_BCF Z hΔ hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH
      hLΛ hμΔ, Kc.isCompact_remainder_BC2, Kc.M₂_eq_edgePiece_union_remainder_BC2, h1, h2, h3, h4,
      h5⟩, C.circleBaseCornersV32_G6C WF Z hrd hrd4 hrdc hprem hθ Kc er h1 h4 h2.subset hcl⟩

/-- **BCF03, the whole row** (the frozen `bcf03_face_partition_BCF03` conclusion on `(Kc, er)`):
every atomic input (`hX1`, `hV`, `hF`, `hsat`) is produced. -/
theorem bcf03_face_partition_final_RM1 {Bs : BoundaryGaf02BasesV2 C.toChain}
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
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000) :
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
          Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) := by
  have hX1 := Kc.remainder_subset_source_BC2 Z (by linarith) hΛ hμ hσc hσs hσs1 hγ34 hLΛ
  exact C.bcf03_face_partition_of_rest_noG6c_BC3d WF Z hrd hrd4 hrdc hprem hθ Kc er hΔ hΛ hμ hτ hσc
    hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ h3βc hγ hγ34 hC hX1
    (C.verticalFace_subset_remainder_RM1 WF Kc er) (C.remainder_inter_frontier_subset_RM1 WF Kc er)
    (Kc.remainder_saturated_actual_RM1 WF Z hX1)

include C in
/-- **The labelled raw graph presentation on the SAME carrier** (separated branch), from the
register numerics only: rows of the actual decomposition (`_RM1` head) and
`exists_rawGraphPresentation_of_rows_BCF04`. -/
theorem boundary_rawGraphPresentation_V32_A4_RM1
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
    (h3βc : 3 * βc ≤ β 2) (hγ0 : 0 ≤ γ) :
    ∃ G : RawGraphPresentation W, ∃ σ : Fin S.packet.cusp.count ≃ Fin G.externalCount,
      ∀ i, Set.range (G.external.torusMap (σ i)) = S.packet.cusp.component i := by
  obtain ⟨dec, geom, Et, hEt, Rw, -⟩ := C.boundary_rows_of_actual_decomposition74_V32_RM1 hβ2 hγ hd
    hK hn hμ hτ hσc hbA hC hε0 hε hγc hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ hΔ hΛ hT hσs hσs1
    hb hs hσL hbη h3b hbH hLΛ hμΔ h3βc hγ0
  exact exists_rawGraphPresentation_of_rows_BCF04 S Rw hEt

end BoundaryGaf02ChainE

/-- **The per-sequence binding** (one `δStar`, one tail `N` per standing sequence; every late
member has a certificate with the rim-product clause on its SAME carrier with the labelled external
boundary), with NO non-register input: only `K ≥ 10` and `A` positive on `(0, ω₃)`. -/
theorem boundary_sequence_binding_final_RM1 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧
    ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
      (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
      (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1))),
      (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) ∧
        curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δStar (n + 1))) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ E : BoundaryTori (W n) (B n).count,
        (∃ Dc : DecompositionCertificate (W n) E, Dc.RimProduct) ∧
        ∀ i, Set.range (E.torusMap i) = (B n).component i := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, -, EW, -, hea, hmain⟩ :=
    exists_boundaryChainE_register_stored_ready_RNUM K hK A hA 0 (cadj := 1) one_pos
  have hδ := (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar_pos
  refine ⟨_, hδ, ?_⟩
  intro W hW g B hcoll
  let Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar :=
    ⟨_, hδ, le_rfl, W, hW, g, B, fun n => (hcoll n).1, fun n => (hcoll n).2⟩
  obtain ⟨V, R, rr, n₀, hR⟩ := hmain Sq
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hm, mr, hsupp⟩ := hR n hn
  obtain ⟨oM⟩ := exists_member_orientation_HB (Sq.W n)
  obtain ⟨Et, ⟨Dc, hDc⟩, hEt⟩ := member_output_to_labelled_certificate_OBDg_A01B EW Sq R hm
    (hm.supply_BSTD2 oM).some hea mr rr
    (fun hsep => by
      obtain ⟨DP, C, -⟩ := hsupp oM _ hsep
      exact ⟨DP, ⟨C⟩⟩)
    (fun _ C => rim3_of_member_records_RM1 EW Sq R hm hea rr C)
  exact ⟨Et, ⟨Dc, hDc⟩, hEt⟩

end DifferentialGeometry.Geometry.Collapse
