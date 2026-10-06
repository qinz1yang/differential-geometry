import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFacesAssembleOBDf
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimPiecesGlobConsumerOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLandingAssembleOBDe

/-!
# The stage lift `hlift` as a theorem (G12): `BoundaryLandingExits74b` from the exports

Lane O-BD1 (by S-BD2f, suffix `_OBDf`), group G12. For a decomposition `dec` with its exports
`geom` and every zero / cusp exit `zc`: the produced stages
(`exists_stageGeometry74b_embedded_OBD`, which needs the explicit input
`hint : dec.bases.edgeParent ⊆ W°`, obstruction O1), the cover (`cutCover_OBD`), the circle facts
(`exists_circleCutFacts_OBDd`), the slim pieces with their end data
(`exists_slim_edgeModels_glob_OBDd`, G10g), the face facts (`exists_faces_OBDf`), then the
assembly `exists_landingExits_of_faces_OBDe`. The only inputs are the register numerics
(`hεr`, `hrd hrd4 hrdc hprem hθ`, obstruction O5) and `hint`.
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

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section EdgeFaces

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **`hlift` as a theorem**: every zero / cusp exit of a decomposition with its exports extends to
the whole boundary landing exits (inputs: `hint` (O1) and the register numerics). -/
theorem exists_landingExits_OBDf (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier))
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (hεr : εr < 1 / 2)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc := by
  obtain ⟨P, -, hιe, hιc⟩ := C.exists_stageGeometry74b_embedded_OBD dec geom hint zc
  have cov := C.cutCover_OBD P hrd hrd4 hrdc hprem hθ
  obtain ⟨G⟩ := C.exists_circleCutFacts_OBDd P geom
  obtain ⟨Sl, -, hnew, hfree, hend⟩ := C.exists_slim_edgeModels_glob_OBDd dec zc P hεr hrd hrd4
    hrdc hprem hθ (C.edgeCutFacts_OBD P hιe.contMDiff geom)
  obtain ⟨faces⟩ := C.exists_faces_OBDf P (C.stageRows_OBDe P geom hιe.contMDiff Sl G) geom hrd
    hrd4 hrdc hprem hθ cov hfree hend
  exact C.exists_landingExits_of_faces_OBDe P geom cov hιe hιc Sl G hnew faces

end BoundaryGaf02ChainE

end EdgeFaces

end DifferentialGeometry.Geometry.Collapse
