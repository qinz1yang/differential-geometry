import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDecompositionV2bOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreProductEmbeddingOCX
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualZeroDomainsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryV2bConsumersBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgePieceCompactBCF
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryToriHCOL
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDiskRimFibreOF1Applications

/-!
# BD1: the boundary geometric exports of ONE decomposition (lane O-BD1, draft 74 BD1)

Draft 74 §4.3 / D74-16, text v3.1 §R on the v2b layer (`BoundaryGeometricExports74b`, named revision
for text v3.2). For the enhanced chain `C` and ANY decomposition `dec` of `C.toChain` on the v2b
layer, every field of the exports that has a row producer in the tree is PROVED here from that row,
with the row's own premises (E4's `r_∂` block and `θ < 1/100`, FAMZ's `εr < 1/2`, the eighteen
BCF02 register premises of BCF2-K for the compactness of `P_e`):

* `cuspCollar_of_product_OBD`: the collar shrink (`cuspCollar`) from E4c and the half-collar kernel
  (`U = Φ(T² × [0, 1/2))`, open by the inverse function theorem with boundary, S-COLLAR G1);
* `cuspFace_V2b_OBD`: the cusp branch of G7 on v2b (F5 on v2b + the component of `∂R_c`);
* `pieces_partial_OBD`: the compactness of `P_e` and `R_c` and `M₂ = P_e ∪ R_c` (G6, first three);
* **`boundaryGeometricExports74b_of_rows_OBD`**: the exports. Fields PROVED: zeroSlim (F5z), cusp
  (E4b), cuspProduct (E4c), cuspCollar, buffer (F4b), frontierM₁ (F4c), frontSlim (F5), faces (G3),
  pieces (first three conjuncts), diskRim (F1, lane O-F1
  `wholeDiskBoundary_eq_wholeCircleFiber_OF1`), cuspFace (modulo `hdisk`). Fields taken as EXPLICIT
  hypotheses, each the verbatim conclusion of a row not yet in the tree: `hG4s` (G4s), `hG6` (the
  five remaining G6 conjuncts), `hG6c` (G6c), `hG7` (G7 partition), `hdisk` (a front off `X₃` misses
  `P_e`, input of BCF03's cusp dichotomy).

NEVER `∀ dec, Nonempty (BoundaryGeometricExports74b C dec)`: here the missing rows are hypotheses on
`dec`; the producer `exists_boundaryGeometricExports74b_OBD` chooses `dec` with them.
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
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

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

/-- **G6, the set-level part**: `P_e` closed gives `R_c = M₂ \ int_{M₂} P_e` compact, and
`M₂ = P_e ∪ R_c`. -/
theorem BoundaryCompactSlimChoiceV2.pieces_partial_OBD
    {C₀ : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ}
    {Bs : BoundaryGaf02BasesV2 C₀} (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (hPe : IsCompact Kc.edgePiece) :
    IsCompact Kc.edgePiece ∧ IsCompact Kc.remainder ∧ Kc.M₂ = Kc.edgePiece ∪ Kc.remainder := by
  refine ⟨hPe, (isClosed_sdiff_relInterior_BCF Kc.isClosed_M₂_BCF Kc.edgePiece).isCompact, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hP : x ∈ Kc.edgePiece
    · exact Or.inl hP
    · exact Or.inr ⟨hx, fun h => hP (relInterior_subset_BCF h)⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The collar shrink from E4c** (`BoundaryGeometricExports74b.cuspCollar`):
`U = Φ(T² × [0, 1/2))` for the E4c product `Φ` is open (half-collar kernel), contains the boundary
component, lies in the core, and its closure misses the front. Premises of E4b. -/
theorem cuspCollar_of_product_OBD {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ i : Fin S.packet.cusp.count, ∃ U : Set W.Carrier, IsOpen U ∧
      S.packet.cusp.component i ⊆ U ∧ U ⊆ C.toChain.cuspCore_BIF i ∧
      Disjoint (closure U) (C.toChain.cuspFront_BIF i) := by
  intro i
  obtain ⟨Φ, hΦ, hrange, h0, h1⟩ :=
    C.bcg06_product_embedding_on_chain_OCX hrd hrd4 hrdc hprem hθ i
  have hbd : ∀ t, W.model.IsBoundaryPoint (Φ (t, iccEnd false)) := by
    intro t
    have hmem : Φ (t, iccEnd false) ∈ S.packet.cusp.component i := by
      rw [← h0]
      exact ⟨t, rfl⟩
    have hb : Φ (t, iccEnd false) ∈ W.model.boundary W.Carrier := by
      rw [← S.packet.cusp.covers]
      exact mem_iUnion.mpr ⟨i, hmem⟩
    exact hb
  obtain ⟨d, -, hdt, -⟩ := HalfCollarHCOL.halfCollar_of_boundary_embedding_HCOL W Φ hΦ hbd
  refine ⟨Φ '' {p | (p.2 : ℝ) < 1 / 2}, hdt ▸ d.open_target, ?_, ?_, ?_⟩
  · rw [← h0]
    rintro _ ⟨t, rfl⟩
    refine ⟨(t, iccEnd false), ?_, rfl⟩
    change ((iccEnd false : Icc (0 : ℝ) 1) : ℝ) < 1 / 2
    simp [iccEnd]
  · rw [← hrange]
    exact image_subset_range _ _
  · rw [← h1]
    exact HalfCollarHCOL.closure_halfCollar_disjoint_HCOL Φ hΦ.contMDiff.continuous
      hΦ.isEmbedding.injective

/-- **BCF03's cusp dichotomy on the v2b layer** (`BoundaryGeometricExports74b.cuspFace`): a front
meeting `X₃` is the whole slim fibre over a point of `K₃ ∩ D₃` (F5 on v2b, the old faces in
`int K₃`), hence inside `S`; a front off `X₃` is a whole component of `∂R_c` missing `P_e`
(`hdisk`, closed `P_e`). Premises of E4b. -/
theorem cuspFace_V2b_OBD {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hPe : IsClosed Kc.edgePiece)
    (hdisk : ∀ i : Fin S.packet.cusp.count, C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅ →
      Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) :
    ∀ i : Fin S.packet.cusp.count,
      (∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y ∧
        C.toChain.cuspFront_BIF i ⊆ Kc.piece) ∨
      (∃ x ∈ Kc.remainder, C.toChain.cuspFront_BIF i =
          connectedComponentIn (frontier Kc.remainder) x ∧
        Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) := by
  intro i
  by_cases h : (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty
  · left
    obtain ⟨y, hyB, hfib⟩ := C.cuspFront_eq_slimFibre_direct_V2b_BGR WF hrd hrd4 hrdc hprem hθ i h
    refine ⟨y, hyB, hfib, ?_⟩
    obtain ⟨p, hp, hpX⟩ := h
    have hF := C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ
    have hHf : C.toChain.cuspFront_BIF i ⊆ frontier C.toChain.M₁_BIFc := fun x hx =>
      hF ▸ Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
    have hpy : C.toChain.stageMap 2 p = y := by
      have hp' : p ∈ Bs.fibre 2 y := hfib ▸ hp
      exact hp'.2
    have hpM : p ∈ C.toChain.M₁_BIFc := C.toChain.isClosed_M₁_BCF.frontier_subset (hHf hp)
    have hyK : y ∈ Kc.K₃ := by
      have h := Kc.slimCut_BIFc.faces_subset ⟨p, ⟨hHf hp, hpX⟩, hpy⟩
      obtain ⟨-, O, -, hyO, hOK⟩ := mem_relInterior_iff_BCF.mp h
      exact hOK ⟨hyO, (Bs.image_eq 2 ▸ ⟨p, hpX, hpy⟩ : y ∈ Bs.base 2)⟩
    have hyD : y ∈ Bs.slimBaseDomain_BIFc := ⟨p, ⟨hpM, hpX⟩, hpy⟩
    intro q hq
    have hq' : q ∈ Bs.fibre 2 y := hfib ▸ hq
    exact ⟨hq'.1, by rw [mem_preimage, hq'.2]; exact ⟨hyK, hyD⟩⟩
  · right
    have hi : C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅ := not_nonempty_iff_eq_empty.mp h
    obtain ⟨p, hp⟩ := (C.isConnected_cuspFront_BCF hrd hrd4 hrdc hprem hθ i).nonempty
    obtain ⟨hpR, hcomp, hd⟩ := C.cuspFront_component_frontier_remainder_BCF Z hrd hrd4 hrdc hprem
      hθ Kc hPe i hi (hdisk i hi) hp
    exact ⟨p, hpR, hcomp, hd⟩

/-- **BD1, the exports of ONE decomposition** (draft 74 BD1 `boundary_geometric_exports74`, on the
v2b layer): for any `dec` of the SAME chain, the fields with a row producer are proved from that row
(F5z, E4b, E4c, collar shrink, F1, F4b, F4c, F5, G3, G6's compactness and union, the cusp
dichotomy); the rows not yet in the tree enter as EXPLICIT hypotheses, each verbatim the field it
supplies: `hG4s` (G4s), `hG6` (the remaining five conjuncts of G6), `hG6c` (G6c), `hG7` (G7's
partition), `hdisk` (a front off `X₃` misses `P_e`). Premises: E4's `r_∂` block and `θ < 1/100`,
`εr < 1/2` (F5z), the eighteen BCF02 register premises (compactness of `P_e`), F1's
`3βc ≤ β₂`, `0 ≤ γ ≤ 3/4`, `100(bder + 1)(1 + bcut + cw₀/Σ₀)ΛΔ < 10⁻⁶` (`c₂ < 10⁻⁵` is stored in
`C.validity`). -/
theorem boundaryGeometricExports74b_of_rows_OBD
    (dec : BoundaryActualDecompositionV2b C.toChain) (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
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
    (hG4s : ∀ ℓ, ∀ y ∈ dec.bases.base 1, dec.edge.faceFun ℓ y = 0 →
      ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
        y ∈ O ∧ ContDiffOn ℝ ∞ (dec.edge.faceFun ℓ) O)
    (hG6 : dec.slim.remainder ⊆ dec.bases.source 0 ∧
      dec.slim.edgePiece ∩ dec.slim.remainder = dec.slim.verticalFace ∧
      dec.slim.remainder ∩ frontier dec.slim.M₂ =
        frontier dec.slim.M₂ \ relInterior_BIF (frontier dec.slim.M₂) dec.slim.horizontalFace ∧
      dec.slim.remainder =
        dec.bases.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' dec.slim.remainder) ∧
      ∀ p ∈ dec.slim.verticalFace ∩ dec.slim.horizontalFace,
        ∃! ℓ, dec.edge.faceFun ℓ (C.toChain.stageMap 1 p) = 0)
    (hG6c : CircleBaseCorners74 dec.slim)
    (hG7 : ∀ x ∈ frontier dec.slim.M₂, ∃ P : Surface.EmbeddedFacePartition_BCF
        (connectedComponentIn (frontier dec.slim.M₂) x),
      (∀ i, ∃ y ∈ C.toChain.stageMap 1 '' dec.slim.horizontalFace,
        Subtype.val '' P.disk i =
          connectedComponentIn (frontier dec.slim.M₂) x ∩ dec.bases.fibre 1 y) ∧
      Subtype.val '' (⋃ j, P.piece j) =
        connectedComponentIn (frontier dec.slim.M₂) x ∩ dec.slim.remainder)
    (hdisk : ∀ i : Fin S.packet.cusp.count, C.toChain.cuspFront_BIF i ∩ dec.bases.source 2 = ∅ →
      Disjoint (C.toChain.cuspFront_BIF i) dec.slim.edgePiece) :
    BoundaryGeometricExports74b C.toChain dec := by
  have hPe := dec.slim.isCompact_edgePiece_BCF dec.zero hΔ hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2
    hσL hbη h3b hbH hLΛ hμΔ
  obtain ⟨hP1, hP2, hP3⟩ := dec.slim.pieces_partial_OBD hPe
  obtain ⟨hF3, hF4, hF5⟩ := bcf01_faces_BCF01 dec.zero dec.slim.slimCut_BIFc
  exact
    { edgeFacesSmooth := hG4s
      zeroSlim := C.zeroFace_eq_slimFibre_direct_V2b_BGR dec.fibres hεr
      cusp := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
      cuspProduct := C.bcg06_product_embedding_on_chain_OCX hrd hrd4 hrdc hprem hθ
      cuspCollar := C.cuspCollar_of_product_OBD hrd hrd4 hrdc hprem hθ
      diskRim := C.wholeDiskBoundary_eq_wholeCircleFiber_OF1 h3βc (by linarith) hγ hγ34
        C.validity.c_two_lt_E4 hC dec.fibres
      buffer := C.toChain.M₁_subset_buffer_BGR _
      frontierM₁ := C.frontier_M₁_BGR dec.zero hrd hrd4 hrdc hprem hθ
      frontSlim := C.cuspFront_eq_slimFibre_direct_V2b_BGR dec.fibres hrd hrd4 hrdc hprem hθ
      faces := ⟨hF3, hF4, hF5⟩
      pieces := ⟨hP1, hP2, hP3, hG6⟩
      circleCorners := hG6c
      partition := hG7
      cuspFace := C.cuspFace_V2b_OBD dec.fibres dec.zero hrd hrd4 hrdc hprem hθ dec.slim
        hPe.isClosed hdisk }

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
