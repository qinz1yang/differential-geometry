import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimsCornersConsumerOBDe
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleTrivOBDd
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeComponentModelsEIMExits

/-!
# The assembly of `BoundaryLandingExits74b` from the slim pieces and the face facts (lane S-BD2e)

Lane O-BD1 (by S-BD2e, suffix `_OBDe`), group G12 (skeleton). On the produced stage geometry `P`:

* `stageRows_OBDe`: the rows `⟨slim, edgeFacts, circleFacts, edgeModels⟩` with
  `edgeFacts := edgeCutFacts_OBD` and `edgeModels := edgeBundle74_models_EIM`;
* `exists_landingExits_of_faces_OBDe`: given the slim pieces `slim : SlimCutPieces74` (G10), the
  circle cut facts (`exists_circleCutFacts_OBDd`), the cover facts, the `rel3` clause of the slim
  exit for the new ends, and the face facts `faces : JunctionFaceFacts74` of the rows, a whole
  `BoundaryLandingExits74b C dec` with `X.zc = zc` (rims and corners are produced:
  `exists_rimsCorners_OBDe`).
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

section Assemble

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc)

/-- **The rows built from the slim pieces and the circle cut facts.** -/
def stageRows_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (hι : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (slim : SlimCutPieces74 P.stageGeometry P.cut) (G : CircleCutFacts74 P.stageGeometry P.cut) :
    StageCutRows74 P.stageGeometry P.cut :=
  ⟨slim, C.edgeCutFacts_OBD P hι geom, G,
    (edgeBundle74_models_EIM P.stageGeometry P.cut (C.edgeCutFacts_OBD P hι geom)).some⟩

include C in
/-- **`BoundaryLandingExits74b` from the slim pieces and the face facts**: every field of the cut
geometry `H` except `slim` and `faces` is produced here. -/
theorem exists_landingExits_of_faces_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hι : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ P.ιedge)
    (hιc : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ P.ιcircle)
    (slim : SlimCutPieces74 P.stageGeometry P.cut) (G : CircleCutFacts74 P.stageGeometry P.cut)
    (hnew : ∀ en : (C.stageRows_OBDe P geom hι.contMDiff slim G).slimPieces.NewEnd,
      ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ a ∧
        ∀ x, (C.stageRows_OBDe P geom hι.contMDiff slim G).slimPieces.endFn en x =
          a (C.toChain.stageMap 2 x))
    (faces : JunctionFaceFacts74 P.stageGeometry P.cut
      (C.stageRows_OBDe P geom hι.contMDiff slim G)) :
    ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc := by
  obtain ⟨rims, ⟨corners⟩⟩ := C.exists_rimsCorners_OBDe P (C.stageRows_OBDe P geom hι.contMDiff
    slim G) geom cov hι hιc hnew faces
  exact ⟨{ zc := zc
           stages := P
           slim := slim
           edgeFacts := C.edgeCutFacts_OBD P hι.contMDiff geom
           edgeModels := (edgeBundle74_models_EIM P.stageGeometry P.cut
             (C.edgeCutFacts_OBD P hι.contMDiff geom)).some
           circleFacts := G
           cover := cov
           faces := faces
           rims := rims
           corners := corners }, rfl⟩

end BoundaryGaf02ChainE

end Assemble

end DifferentialGeometry.Geometry.Collapse
