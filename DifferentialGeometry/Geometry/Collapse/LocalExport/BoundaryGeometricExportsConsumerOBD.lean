import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGeometricExportsProducerOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFaceCountsBCF

/-!
# Consumers of the BD1 exports (lane O-BD1)

* `BoundaryGeometricExports74b.faceCounts_OBD`: the exports' G7 partition with G7' (FC40's disk
  counts): on every component of `∂M₂` an embedded face partition whose disks are whole edge
  fibres, with two disks on a sphere face and none on a torus face;
* `BoundaryGeometricExports74b.cuspCollar_closure_subset_OBD`: the collar shrink and the E4c
  product give a closed collar `cl U ⊆ C_b \ H_b` around the boundary component;
* `BoundaryGaf02ChainE.exists_dec_faceCounts_OBD`: the producer composed with the counts (the
  decomposition `dec` and its exports chosen together, then consumed).
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

section Records

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {dec : BoundaryActualDecompositionV2b C}

/-- **G7 + G7' from the exports**: on every component of `∂M₂` an embedded face partition with the
disks = whole edge fibres over `f₂(H_e)`, two disks on a sphere face, none on a torus face. -/
theorem BoundaryGeometricExports74b.faceCounts_OBD (geom : BoundaryGeometricExports74b C dec) :
    ∀ x ∈ frontier dec.slim.M₂, ∃ P : Surface.EmbeddedFacePartition_BCF
        (connectedComponentIn (frontier dec.slim.M₂) x),
      (∀ i, ∃ y ∈ C.stageMap 1 '' dec.slim.horizontalFace,
        Subtype.val '' P.disk i = connectedComponentIn (frontier dec.slim.M₂) x ∩
          dec.bases.fibre 1 y) ∧
      (Nonempty (connectedComponentIn (frontier dec.slim.M₂) x ≃ₜ SphereTwo) →
        P.diskCount = 2) ∧
      (Nonempty (connectedComponentIn (frontier dec.slim.M₂) x ≃ₜ Circle × Circle) →
        P.diskCount = 0) := by
  intro x hx
  obtain ⟨P, hdisk, -⟩ := geom.partition x hx
  exact ⟨P, hdisk, dec.slim.bcf03_counts_BCF03 x hx P⟩

/-- **The closed collar of a boundary component** from the exports: the collar shrink `U` (open,
around the component, inside the core) has closure inside `C_b \ H_b` (`C_b` closed: the E4c
product is a compact image). -/
theorem BoundaryGeometricExports74b.cuspCollar_closure_subset_OBD
    (geom : BoundaryGeometricExports74b C dec) (i : Fin S.packet.cusp.count) :
    ∃ U : Set W.Carrier, IsOpen U ∧ S.packet.cusp.component i ⊆ U ∧
      closure U ⊆ C.cuspCore_BIF i \ C.cuspFront_BIF i := by
  obtain ⟨U, hU, hcU, hUC, hdis⟩ := geom.cuspCollar i
  obtain ⟨Ψ, hΨ, hrange, -, -⟩ := geom.cuspProduct i
  have hCc : IsClosed (C.cuspCore_BIF i) := by
    rw [← hrange]
    exact (isCompact_range hΨ.contMDiff.continuous).isClosed
  refine ⟨U, hU, hcU, fun x hx => ⟨hCc.closure_subset_iff.mpr hUC hx, fun hxF => ?_⟩⟩
  exact Set.disjoint_left.mp hdis hx hxF

end Records

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The BD1 producer, consumed**: a decomposition of the chain on the A4 bases `Bs`, chosen with
its exports, whose `∂M₂` face partitions have the FC40 counts. Hypotheses: those of
`exists_boundaryGeometricExports74b_OBD`, passed through unchanged. -/
theorem exists_dec_faceCounts_OBD (Bs : BoundaryGaf02BasesV2 C.toChain)
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
      ∀ x ∈ frontier dec.slim.M₂, ∃ P : Surface.EmbeddedFacePartition_BCF
        (connectedComponentIn (frontier dec.slim.M₂) x),
      (Nonempty (connectedComponentIn (frontier dec.slim.M₂) x ≃ₜ SphereTwo) →
        P.diskCount = 2) ∧
      (Nonempty (connectedComponentIn (frontier dec.slim.M₂) x ≃ₜ Circle × Circle) →
        P.diskCount = 0) := by
  obtain ⟨dec, hB, geom⟩ := C.exists_boundaryGeometricExports74b_OBD Bs WF hεr he hrd hrd4 hrdc
    hprem hθ hΔ hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ h3βc hγ hγ34 hC hG4
    hG6 hG6c hG7 hdisk
  refine ⟨dec, hB, fun x hx => ?_⟩
  obtain ⟨P, -, h2, h0⟩ := geom.faceCounts_OBD x hx
  exact ⟨P, h2, h0⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
