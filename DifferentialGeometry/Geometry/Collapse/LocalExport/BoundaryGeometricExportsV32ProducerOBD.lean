import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGeometricExportsV32OBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGeometricExportsProducerOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsA4V2bOBD

/-!
# The V32 exports producer and the V2b / V32 landing (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G4 (review 77 D77-2, D77-7, D77-10: "add the V32
exports producer to the frozen targets"; "BCF04 needs its own V2b landing").

* **`exists_boundaryGeometricExports74V32_OBD Bs WF …`**: `∃ dec, dec.bases = Bs ∧
  BoundaryGeometricExports74V32 C.toChain dec` — `dec` and `geom` chosen together (D74-16), the
  corner input `hG6c` now the V32 corner model (G6c's conclusion in text v3.2, R9); the other
  rows still missing in the tree stay explicit as in O-BD1 G1 (`hG4`, `hG6`, `hG7`, `hdisk`);
* `exists_boundaryGeometricExports74V32_A4_OBD`: the same with A4 produced (O-WF2);
* **`boundary_rows_of_actual_decomposition74_V32_OBD C dec geom Q (E4b) hlift`**: the frozen v3.2
  head (`geom : BoundaryGeometricExports74V32`, `dec` on V2b, link `BoundaryRowsLink74b`), the
  stage lift with the cut geometry over the produced zero / cusp exit as the input `hlift`;
* `boundary_graphPresentation_of_actual_decomposition_V32_BCF04_OBD` (G8 composed, BCF04 on its
  OWN V2b landing) and `boundary_strongCertificate_V32_A4_OBD` (§R final shape, A4 produced).
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

/-- **The V32 exports producer** (D77-2 / D77-10; `dec` and `geom` chosen together): the v2b
decomposition on the given A4 output with the V32 exports; corner input = the V32 corner model. -/
theorem exists_boundaryGeometricExports74V32_OBD (Bs : BoundaryGaf02BasesV2 C.toChain)
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (hΔ : 2 ≤ Δ)
    (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (h3βc : 3 * βc ≤ β 2) (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hG4 : BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      ∃ er : BoundaryRelativeEdgeRestrictionV2 Kc, ∀ ℓ, ∀ y ∈ Bs.base 1, er.faceFun ℓ y = 0 →
        ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
          y ∈ O ∧ ContDiffOn ℝ ∞ (er.faceFun ℓ) O)
    (hG6 : BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ (Kc : BoundaryCompactSlimChoiceV2 Bs)
      (er : BoundaryRelativeEdgeRestrictionV2 Kc),
      Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder = Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.toChain.stageMap 1 p) = 0)
    (hG6c : BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      BoundaryRelativeEdgeRestrictionV2 Kc → CircleBaseCornersV32 Kc)
    (hG7 : BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      BoundaryRelativeEdgeRestrictionV2 Kc → ∀ x ∈ frontier Kc.M₂,
      ∃ P : Surface.EmbeddedFacePartition_BCF (connectedComponentIn (frontier Kc.M₂) x),
        (∀ i, ∃ y ∈ C.toChain.stageMap 1 '' Kc.horizontalFace,
          Subtype.val '' P.disk i = connectedComponentIn (frontier Kc.M₂) x ∩ Bs.fibre 1 y) ∧
        Subtype.val '' (⋃ j, P.piece j) = connectedComponentIn (frontier Kc.M₂) x ∩ Kc.remainder)
    (hdisk : BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      ∀ i : Fin S.packet.cusp.count, C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅ →
        Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain, dec.bases = Bs ∧
      BoundaryGeometricExports74V32 C.toChain dec := by
  obtain ⟨Z⟩ := C.exists_boundaryActualZeroDomains_BGR WF hεr he hrd hrd4 hrdc hprem hθ
  obtain ⟨Kc⟩ := C.exists_boundaryCompactSlimChoiceV2_OBD WF Z hεr hrd hrd4 hrdc hprem hθ
  obtain ⟨er, her⟩ := hG4 Z Kc
  let dec : BoundaryActualDecompositionV2b C.toChain :=
    { bases := Bs, fibres := WF, zero := Z, slim := Kc, edge := er }
  have geom := C.boundaryGeometricExports74b_of_rows_OBD dec hεr hrd hrd4 hrdc hprem hθ hΔ hΛ hμ
    hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ h3βc hγ hγ34 hC her (hG6 Z Kc er)
    (hG6c Z Kc er).toCorners74 (hG7 Z Kc er) (hdisk Z Kc)
  exact ⟨dec, rfl, BoundaryGeometricExports74V32.ofExports74b_OBD geom (hG6c Z Kc er)⟩

/-- **The V32 exports producer with A4 produced** (O-WF2's `exists_boundaryGaf02BasesV2b_OWF`). -/
theorem exists_boundaryGeometricExports74V32_A4_OBD
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
        Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74V32 C.toChain dec := by
  obtain ⟨Bs, WF⟩ := C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd hK hn hμ hτ hσc hbA
    C.validity.c_two_lt_E4 hC hε0 hε hγc hγc1 hβc1
  have hn' : 1140 * Δ ≤ 35 * (n : ℝ) := by linarith
  have hβ2' : β 2 < 1 / 1000000 := by linarith
  have hγ34 : γ ≤ 3 / 4 := by linarith
  obtain ⟨dec, -, geom⟩ := C.exists_boundaryGeometricExports74V32_OBD Bs WF hεr he hrd hrd4 hrdc
    hprem hθ hΔ hΛ hμ hτ hσc hn' hT hσs hσs1 hb hs hβ2' hσL hbη h3b hbH hLΛ hμΔ h3βc hγ0 hγ34 hC
    (hG4 Bs WF) (hG6 Bs WF) (hG6c Bs WF) (hG7 Bs WF) (hdisk Bs WF)
  exact ⟨dec, geom⟩

/-- **The frozen v3.2 head on its OWN V2b landing** (`dec` on V2b, `geom` V32, link
`BoundaryRowsLink74b`; D77-1 R2, D77-7): the zero / cusp exit produced (G3), the stage lift with the
cut geometry over it the input `hlift`. -/
theorem boundary_rows_of_actual_decomposition74_V32_OBD
    (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74V32 C.toChain dec)
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hlift : ∀ zc : BoundaryZeroCuspExit74b C.toChain dec,
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
      ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink74b C.toChain dec Et Rw :=
  C.boundary_rows_of_actual_decomposition74b_OBD dec geom.toExports74b Q hrd hrd4 hrdc hprem hθ
    hlift

/-- **G8 (separated branch) composed on the V2b / V32 landing** (BCF04's own V2b landing, D77-7):
the certificate with the rim-product clause on tori with the packet's labels. -/
theorem boundary_graphPresentation_of_actual_decomposition_V32_BCF04_OBD
    (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74V32 C.toChain dec)
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
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
    C.boundary_rows_of_actual_decomposition74_V32_OBD dec geom Q hrd hrd4 hrdc hprem hθ hlift
  exact boundary_graphPresentation_of_rows_BCF04 S Rw hEt

/-- **§R final shape on V2b / V32 with A4 produced**: the decomposition with its V32 exports, the
packet-labelled tori, the linked rows and the strong certificate on the SAME rows. -/
theorem boundary_strongCertificate_V32_A4_OBD
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
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
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
    C.boundary_rows_of_actual_decomposition74_V32_OBD dec geom Q hrd hrd4 hrdc hprem hθ
      (hlift dec)
  exact ⟨dec, geom, Et, hEt, Rw, L, exists_strongCertificate_of_rows_GFIN Rw⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
