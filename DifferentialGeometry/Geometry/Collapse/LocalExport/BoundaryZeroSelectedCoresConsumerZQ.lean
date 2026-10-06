import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGeometricExportsV32ProducerOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroSelectedCoresZQ

/-!
# Consumers of the produced Z1 cores: the V32 / A4 full heads (lane S-ZQ, suffix `_ZQ`), G1

`BoundarySupply.zeroSelectedCores_ZQ` (BoundaryZeroSelectedCoresZQ) inhabits the type of the input
`Q` of the boundary full heads of BoundaryGeometricExportsV32ProducerOBD. Here `Q` is dropped from
them and every other input is unchanged:

* `boundary_rows_of_actual_decomposition74_V32_ZQ`: the frozen v3.2 head on its own V2b landing;
  inputs: `dec`, `geom`, the numerics and the stage lift `hlift`;
* `boundary_graphPresentation_of_actual_decomposition_V32_BCF04_ZQ`: the same for the G8
  certificate with the rim-product clause;
* `boundary_strongCertificate_V32_A4_ZQ`: §R final shape with A4 produced; inputs: the register
  numerics, the exports rows `hG4 / hG6 / hG6c / hG7 / hdisk` and `hlift`.
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

/-- **The frozen v3.2 head on its OWN V2b landing, Z1 cores produced** (`dec` on V2b, `geom` V32,
link `BoundaryRowsLink74b`): `Q` is `S.zeroSelectedCores_ZQ`, the stage lift `hlift` is the only
input besides the decomposition and its exports. -/
theorem boundary_rows_of_actual_decomposition74_V32_ZQ
    (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74V32 C.toChain dec)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hlift : ∀ zc : BoundaryZeroCuspExit74b C.toChain dec,
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
      ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink74b C.toChain dec Et Rw :=
  C.boundary_rows_of_actual_decomposition74b_OBD dec geom.toExports74b S.zeroSelectedCores_ZQ hrd
    hrd4 hrdc hprem hθ hlift

/-- **G8 (separated branch) on the V2b / V32 landing, Z1 cores produced** (BCF04's own V2b
landing): the certificate with the rim-product clause on tori with the packet's labels. -/
theorem boundary_graphPresentation_of_actual_decomposition_V32_BCF04_ZQ
    (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74V32 C.toChain dec)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hlift : ∀ zc : BoundaryZeroCuspExit74b C.toChain dec,
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = S.packet.cusp.component i := by
  obtain ⟨Et, hEt, Rw, -⟩ :=
    C.boundary_rows_of_actual_decomposition74_V32_ZQ dec geom hrd hrd4 hrdc hprem hθ hlift
  exact boundary_graphPresentation_of_rows_BCF04 S Rw hEt

/-- **§R final shape on V2b / V32 with A4 and the Z1 cores produced**: the decomposition with its
V32 exports, the packet-labelled tori, the linked rows and the strong certificate on the SAME
rows. Inputs: the register numerics, the exports rows `hG4 / hG6 / hG6c / hG7 / hdisk`, and the
stage lift `hlift`; NO `Q`. -/
theorem boundary_strongCertificate_V32_A4_ZQ
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
    (hG6 : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ (Kc : BoundaryCompactSlimChoiceV2 Bs)
      (er : BoundaryRelativeEdgeRestrictionV2 Kc),
      Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder =
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.toChain.stageMap 1 p) = 0)
    (hG6c : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      BoundaryRelativeEdgeRestrictionV2 Kc → CircleBaseCornersV32 Kc)
    (hG7 : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      BoundaryRelativeEdgeRestrictionV2 Kc → ∀ x ∈ frontier Kc.M₂,
      ∃ P : Surface.EmbeddedFacePartition_BCF (connectedComponentIn (frontier Kc.M₂) x),
        (∀ i, ∃ y ∈ C.toChain.stageMap 1 '' Kc.horizontalFace,
          Subtype.val '' P.disk i = connectedComponentIn (frontier Kc.M₂) x ∩ Bs.fibre 1 y) ∧
        Subtype.val '' (⋃ j, P.piece j) = connectedComponentIn (frontier Kc.M₂) x ∩ Kc.remainder)
    (hdisk : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      ∀ i : Fin S.packet.cusp.count, C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅ →
        Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece)
    (hlift : ∀ (dec : BoundaryActualDecompositionV2b C.toChain)
      (zc : BoundaryZeroCuspExit74b C.toChain dec),
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74V32 C.toChain dec ∧
      ∃ Et : BoundaryTori W S.packet.cusp.count,
        (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
        ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink74b C.toChain dec Et Rw ∧
          Nonempty (StrongCertificate W Et) := by
  obtain ⟨dec, geom⟩ := C.exists_boundaryGeometricExports74V32_A4_OBD hβ2 hγ hd hK hn hμ hτ hσc
    hbA hC hε0 hε hγc hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ hΔ hΛ hT hσs hσs1 hb hs hσL hbη h3b
    hbH hLΛ hμΔ h3βc hγ0 hG4 hG6 hG6c hG7 hdisk
  obtain ⟨Et, hEt, Rw, L⟩ :=
    C.boundary_rows_of_actual_decomposition74_V32_ZQ dec geom hrd hrd4 hrdc hprem hθ (hlift dec)
  exact ⟨dec, geom, Et, hEt, Rw, L, exists_strongCertificate_of_rows_GFIN Rw⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
