import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLandingExitsLND
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDecompositionV2bOBD

/-!
# The boundary landing exits on the v2b decomposition (lane O-BD2)

Lane O-BD2 (successor of O-BD1, suffix `_OBD`), group G3a. The exits records of S-LANDING G3b
(`BoundaryLandingExitsLND`) restated VERBATIM on `dec : BoundaryActualDecompositionV2b C` (the named
revision for text v3.2: the decomposition lives on the whole-fibre layer v2b, lead 21:2x). No field
uses the buffer of the whole-fibre layer, so the text is token for token that of the v2 records:

* `BoundaryZeroCuspExit74b C dec`: tori `Et` with the packet's labels, the zero domains linked to
  `C.actualZeroDomain_BIFc` and `dec.zero.defFn`, the cusp cores linked to the cores, fronts and
  `u_b − 40 v_b`;
* `BoundaryStageGeometry74b zc`: the three stages over `W`, embedded in the ambient base by `ι_j`
  (`StageIdentSrc_LND74` with the sources of `dec.bases`), height, level, the cut choice
  identified with `dec.slim`;
* `BoundaryLandingExits74b C dec`: those and the cut-dependent facts in the assembler's vocabulary;
  `BoundaryLandingExits74b.geometry` the cut geometry `H`.

The stage geometry `A` is S-LANDING's `assembleBoundaryStages74` (it does not depend on `dec`).
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

section Exits

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **The tori, the zero rows and the cusp rows of the boundary landing**: the boundary tori `Et`
numbered by the packet's cusp components, the zero domains linked to the chain's actual zero
domains and the decomposition's global defining functions, the cusp cores linked to the chain's
cusp cores, fronts and `cuspFn = u_b − 40 v_b`. -/
structure BoundaryZeroCuspExit74b (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (dec : BoundaryActualDecompositionV2b C) where
  Et : BoundaryTori W S.packet.cusp.count
  labels : ∀ i, range (Et.torusMap i) = S.packet.cusp.component i
  zero : ZeroDomains W
  zero_link : ∃ σ : Fin zero.count ≃ S.ZeroIdx_BAUGC, ∀ k,
    range (zero.piece k).map = C.actualZeroDomain_BIFc (σ k) ∧
      zero.ratio k = dec.zero.defFn (σ k)
  cusp : CuspCores W Et
  cusp_link : ∀ i, range (cusp.piece i).map = C.cuspCore_BIF i ∧
    (range fun t => (cusp.piece i).map (cusp.product i (t, iccEnd true))) = C.cuspFront_BIF i ∧
    ∀ x ∈ cusp.near i,
      cusp.cuspFn i x = chainBoundaryU_BCG6K C.E i x - 40 * chainBoundaryV_BCG6K C.E i x

/-- **`BoundaryStageGeometry74b C dec zc`**: the three stages of `A` over `W` identified with the
decomposition's stage maps and sources, and the abstract cut choice identified with `dec.slim`. -/
structure BoundaryStageGeometry74b {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {dec : BoundaryActualDecompositionV2b C} (zc : BoundaryZeroCuspExit74b C dec) where
  slim : SlimStage74 W
  edge : EdgeStage74 W
  circle : StageProj74 W 2
  ιslim : slim.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)
  ιedge : edge.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)
  ιcircle : circle.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)
  slim_ident : StageIdentSrc_LND74 slim.toStageProj74 (C.stageMap 2) ιslim (dec.bases.source 2)
  edge_ident : StageIdentSrc_LND74 edge.toStageProj74 (C.stageMap 1) ιedge dec.bases.edgeParent
  circle_ident : StageIdentSrc_LND74 circle (C.stageMap 0) ιcircle (dec.bases.source 0)
  edge_range : range ιedge ⊆ dec.bases.base 1
  circle_range : range ιcircle ⊆ dec.bases.base 0
  edge_height : ∀ x : edge.parent, edge.height x = C.heightRatio x
  edge_level : edge.level = 4 * Δ
  cut : StageCutChoice74 (assembleBoundaryStages74 zc.zero zc.cusp slim edge circle)
  cut_D₃ : ιslim '' cut.D₃ = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc
  cut_C₂ : ιedge '' cut.C₂ = C.stageMap 1 '' dec.slim.edgePiece
  cut_C₁ : ιcircle '' cut.C₁ = C.stageMap 0 '' dec.slim.remainder
  comp : ActualComponent cut.D₃ ≃ ActualComponent (dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc)
  comp_eq : ∀ c, ιslim '' c.1 = (comp c).1
  edgePiece_eq : dec.slim.edgePiece = dec.bases.edgeParent ∩ C.stageMap 1 ⁻¹' (ιedge '' cut.C₂) ∩
    {p | C.heightRatio p ≤ 4 * Δ}

/-- The stage geometry of the exits (`A` of the abstract assembler). -/
abbrev BoundaryStageGeometry74b.stageGeometry {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {dec : BoundaryActualDecompositionV2b C} {zc : BoundaryZeroCuspExit74b C dec}
    (P : BoundaryStageGeometry74b zc) : SmoothStageGeometry74 W zc.Et :=
  assembleBoundaryStages74 zc.zero zc.cusp P.slim P.edge P.circle

/-- **`BoundaryLandingExits74b C dec`**: the zero / cusp rows, the stages, and the cut-dependent
facts of the boundary rows (slim pieces, edge facts and components, circle facts, FDC04 cover,
faces, rims, corners), in the assembler's vocabulary. -/
structure BoundaryLandingExits74b (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (dec : BoundaryActualDecompositionV2b C) where
  zc : BoundaryZeroCuspExit74b C dec
  stages : BoundaryStageGeometry74b zc
  slim : SlimCutPieces74 stages.stageGeometry stages.cut
  edgeFacts : EdgeCutFacts74 stages.stageGeometry stages.cut
  edgeModels : EdgeComponentModels (edgeBundle74 stages.stageGeometry stages.cut edgeFacts)
  circleFacts : CircleCutFacts74 stages.stageGeometry stages.cut
  cover : CutCoverFacts74 stages.stageGeometry stages.cut
  faces : JunctionFaceFacts74 stages.stageGeometry stages.cut
    ⟨slim, edgeFacts, circleFacts, edgeModels⟩
  rims : JunctionRimFacts74 stages.stageGeometry stages.cut
    ⟨slim, edgeFacts, circleFacts, edgeModels⟩
  corners : CornerCutFacts74 faces rims

/-- The cut geometry `H` of the boundary exits. -/
def BoundaryLandingExits74b.geometry {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {dec : BoundaryActualDecompositionV2b C} (X : BoundaryLandingExits74b C dec) :
    StageCutGeometry74 X.stages.stageGeometry X.stages.cut where
  rows := ⟨X.slim, X.edgeFacts, X.circleFacts, X.edgeModels⟩
  cover := X.cover
  faces := X.faces
  rims := X.rims
  corners := X.corners

end Exits

end DifferentialGeometry.Geometry.Collapse
