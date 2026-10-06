import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCaaMemberV2bOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimBaseCuspConsumerOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGeometricExportsProducerOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesV2bProductionOWF

/-!
# The boundary landing with A4 produced (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G5. A4 whole now exists
(`BoundaryGaf02ChainE.exists_boundaryGaf02BasesV2b_OWF`, lane O-WF2 G7 + G8: `∃ Bs, WF v2b` from
register premises). The `(Bs, WF)` data of the exports producer, of the BD2 head, of the §R form
and of 07.g3 are replaced by that call; the A4 premises are those of O-WF2's theorem (with
`c 2 < 10⁻⁵` read off the chain's validity), the producer's numeric premises are kept (`1140 Δ ≤
35 n`, `β 2 < 10⁻⁶`, `γ ≤ 3/4` follow from A4's). The rows still missing in the tree stay the
explicit inputs `hG4` (G4 / G4s), `hG6` (G6), `hG6c` (G6c), `hG7` (G7), `hdisk` (S-BCF03 G7), now
quantified over every A4 output; the stage lift with the cut geometry is `hlift`.

* `exists_boundaryGeometricExports74b_A4_OBD`: `∃ dec, BoundaryGeometricExports74b C.toChain dec`;
* **`boundary_strongCertificate_A4_OBD`**: `∃ dec, exports ∧ ∃ Et, labels ∧ ∃ Rw,
  BoundaryRowsLink74b ∧ Nonempty (StrongCertificate W Et)` (§R final shape, SAME rows);
* `caaMember_A4_OBD`: the CAA02 / BBR03 member conclusion on `B`;
* `bcg07_clause_g3_A4_OBD`: 07.g3 (D77-6 shape) on the produced A4 output and zero domains.
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

/-- **The exports producer with A4 produced**: `dec` and `geom` chosen together on the A4 output
of O-WF2 (D74-16: never `∀ dec`). -/
theorem exists_boundaryGeometricExports74b_A4_OBD
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
      BoundaryRelativeEdgeRestrictionV2 Kc → CircleBaseCorners74 Kc)
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
        Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74b C.toChain dec := by
  obtain ⟨Bs, WF⟩ := C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd hK hn hμ hτ hσc hbA
    C.validity.c_two_lt_E4 hC hε0 hε hγc hγc1 hβc1
  have hn' : 1140 * Δ ≤ 35 * (n : ℝ) := by linarith
  have hβ2' : β 2 < 1 / 1000000 := by linarith
  have hγ34 : γ ≤ 3 / 4 := by linarith
  obtain ⟨dec, -, geom⟩ := C.exists_boundaryGeometricExports74b_OBD Bs WF hεr he hrd hrd4 hrdc
    hprem hθ hΔ hΛ hμ hτ hσc hn' hT hσs hσs1 hb hs hβ2' hσL hbη h3b hbH hLΛ hμΔ h3βc hγ0 hγ34 hC
    (hG4 Bs WF) (hG6 Bs WF) (hG6c Bs WF) (hG7 Bs WF) (hdisk Bs WF)
  exact ⟨dec, geom⟩

/-- **§R final shape with A4 produced** (D74-16 / D76-5): the decomposition and its exports, the
packet-labelled tori, the rows linked to the decomposition and the strong certificate on the SAME
rows. -/
theorem boundary_strongCertificate_A4_OBD
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
      BoundaryRelativeEdgeRestrictionV2 Kc → CircleBaseCorners74 Kc)
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
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
    (hlift : ∀ (dec : BoundaryActualDecompositionV2b C.toChain)
      (zc : BoundaryZeroCuspExit74b C.toChain dec),
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain, BoundaryGeometricExports74b C.toChain dec ∧
      ∃ Et : BoundaryTori W S.packet.cusp.count,
        (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
        ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink74b C.toChain dec Et Rw ∧
          Nonempty (StrongCertificate W Et) := by
  obtain ⟨dec, geom⟩ := C.exists_boundaryGeometricExports74b_A4_OBD hβ2 hγ hd hK hn hμ hτ hσc hbA hC
    hε0 hε hγc hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ hΔ hΛ hT hσs hσs1 hb hs hσL hbη h3b hbH hLΛ
    hμΔ h3βc hγ0 hG4 hG6 hG6c hG7 hdisk
  exact ⟨dec, geom, C.boundary_strongCertificate_of_actual_decomposition74b_OBD dec geom Q hrd
    hrd4 hrdc hprem hθ (hlift dec)⟩

/-- **The CAA02 / BBR03 member conclusion with A4 produced**. -/
theorem caaMember_A4_OBD
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
      BoundaryRelativeEdgeRestrictionV2 Kc → CircleBaseCorners74 Kc)
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
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
    (hlift : ∀ (dec : BoundaryActualDecompositionV2b C.toChain)
      (zc : BoundaryZeroCuspExit74b C.toChain dec),
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ E : BoundaryTori W B.count, (∃ Dc : DecompositionCertificate W E, Dc.RimProduct) ∧
      ∀ i, range (E.torusMap i) = B.component i := by
  obtain ⟨dec, geom⟩ := C.exists_boundaryGeometricExports74b_A4_OBD hβ2 hγ hd hK hn hμ hτ hσc hbA hC
    hε0 hε hγc hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ hΔ hΛ hT hσs hσs1 hb hs hσL hbη h3b hbH hLΛ
    hμΔ h3βc hγ0 hG4 hG6 hG6c hG7 hdisk
  exact C.caaMember_of_actual_decomposition74b_OBD dec geom Q hrd hrd4 hrdc hprem hθ (hlift dec)

/-- **07.g3 (D77-6 shape) with A4 produced**: on O-WF2's A4 output and the produced zero domains,
at every cusp whose front meets `X₃`. -/
theorem bcg07_clause_g3_A4_OBD
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K)
    (hn : 32 * (1000000 * Δ) ≤ (n : ℝ)) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hbA : b ≤ 1 / (1000 * Δ))
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs ∧
      ∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
      ∃ y₀ ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y₀ ∧
        cuspRatioBase_OBD i y₀ = 0 ∧
        (∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
          y₀ ∈ O ∧ ∀ y ∈ Bs.base 2 ∩ O, (y ∈ Bs.slimBaseDomain_BIFc ↔ 0 ≤ cuspBaseCLM_OBD i y)) ∧
        ∃ σ : EuclideanSpace ℝ (Fin 1) →
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count),
          σ 0 = y₀ ∧ ContDiff ℝ ∞ σ ∧ (∃ O, IsOpen O ∧ range σ = Bs.base 2 ∩ O) ∧
          fderiv ℝ (cuspRatioBase_OBD i ∘ σ) 0 ≠ 0 := by
  obtain ⟨Bs, WF⟩ := C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd hK hn hμ hτ hσc hbA
    C.validity.c_two_lt_E4 hC hε0 hε hγc hγc1 hβc1
  obtain ⟨Z⟩ := C.exists_boundaryActualZeroDomains_BGR WF hεr he hrd hrd4 hrdc hprem hθ
  exact ⟨Bs, WF, fun i hX => C.bcg07_clause_g3_OBD WF Z hrd hrd4 hrdc hprem hθ i hX⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
