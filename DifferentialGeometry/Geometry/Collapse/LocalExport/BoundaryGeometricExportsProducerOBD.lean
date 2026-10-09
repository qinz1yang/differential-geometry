import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGeometricExportsOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimChoiceV2bOBD

/-!
# BD1 producer: the decomposition and its exports chosen TOGETHER (lane O-BD1, draft 74 BD1)

D74-16: never `∀ dec, Nonempty (BoundaryGeometricExports74b C dec)`; the producer chooses `dec` and
the exports together. From the A4 output `(Bs, WF)` of the SAME enhanced chain `C` (v2b layer, named
revision for text v3.2):

* `Z` = F3 `exists_boundaryActualZeroDomains_BGR` (S-BCG-ROWS2 G32; `εr < 1/2`, `e ≤ 1/1000`, E4);
* `Kc` = G1 `exists_boundaryCompactSlimChoiceV2_OBD` (BCF01 on v2b);
* `er` = G4 (`hG4`, NOT in the tree: the labelled relative edge restriction producer with G4s);
* the exports = `boundaryGeometricExports74b_of_rows_OBD`, with the rows not in the tree as
  explicit hypotheses in the form of their frozen heads (∀ over the objects they are stated on):
  `hG6` / `hG6c` / `hG7` (G6's five remaining conjuncts, G6c, G7, on every `Z`, `Kc`, `er`),
  `hdisk` (BCF03's front-off-`X₃` input, on every `Z`, `Kc`); F1 is O-F1's producer.

**`exists_boundaryGeometricExports74b_OBD`**: `∃ dec, dec.bases = Bs ∧ BoundaryGeometricExports74b
C.toChain dec`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly

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

/-- **BD1 producer** (draft 74 BD1 `boundary_geometric_exports74`, v2b layer): from the A4 output
`(Bs, WF)` of the SAME chain, a decomposition `dec` with bases `Bs` (zero domains by F3, slim choice
by BCF01 G1, edge restriction by G4 = `hG4`) TOGETHER with its exports. The rows not in the tree are
the explicit hypotheses `hG4`, `hG6`, `hG6c`, `hG7`, `hdisk` (frozen-head form). Premises:
`εr < 1/2`, `e ≤ 1/1000` (F3), E4's `r_∂` block and `θ < 1/100`, the eighteen BCF02 register
premises (compactness of `P_e`), F1's `h3βc hγ hγ34 hC`. -/
theorem exists_boundaryGeometricExports74b_OBD (Bs : BoundaryGaf02BasesV2 C.toChain)
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
      BoundaryRelativeEdgeRestrictionV2 Kc → CircleBaseCorners74 Kc)
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
      BoundaryGeometricExports74b C.toChain dec := by
  obtain ⟨Z⟩ := C.exists_boundaryActualZeroDomains_BGR WF hεr he hrd hrd4 hrdc hprem hθ
  obtain ⟨Kc⟩ := C.exists_boundaryCompactSlimChoiceV2_OBD WF Z hεr hrd hrd4 hrdc hprem hθ
  obtain ⟨er, her⟩ := hG4 Z Kc
  let dec : BoundaryActualDecompositionV2b C.toChain :=
    { bases := Bs, fibres := WF, zero := Z, slim := Kc, edge := er }
  exact ⟨dec, rfl, C.boundaryGeometricExports74b_of_rows_OBD dec hεr hrd hrd4 hrdc hprem hθ hΔ hΛ hμ
    hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ h3βc hγ hγ34 hC her (hG6 Z Kc er)
    (hG6c Z Kc er) (hG7 Z Kc er) (hdisk Z Kc)⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
