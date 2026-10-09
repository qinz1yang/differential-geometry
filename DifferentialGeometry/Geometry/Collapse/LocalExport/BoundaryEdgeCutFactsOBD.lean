import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRankTwoOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeFibreDiskOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCbaseDomainOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutFactsOBD

/-!
# `EdgeCutFacts74` for the produced stages (lane S-BD2c)

Lane O-BD1 (by S-BD2c, suffix `_OBD`), group G8 (hlift, the cut facts `H`, structure
`EdgeCutFacts74`): the five fields `rank_two`, `proper`, `fibre_disk`, `cbase_compact`,
`cbase_domain` for ANY produced `P : BoundaryStageGeometry74b zc` with smooth edge inclusion (the
smooth-`ι` strengthening `exists_stageGeometry74b_smooth_OBD` of G7e provides it).
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

section EdgeCutFacts

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}

include C in
/-- **`EdgeCutFacts74` of the produced stages**: all five fields (the structure is a `Prop`), for a
stage geometry whose edge inclusion is smooth. -/
theorem edgeCutFacts_OBD (P : BoundaryStageGeometry74b zc)
    (hι : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (geom : BoundaryGeometricExports74b C.toChain dec) :
    EdgeCutFacts74 P.stageGeometry P.cut where
  rank_two := P.edge_rank_two_OBD hι
  proper := P.edge_proper_OBD
  fibre_disk := P.edge_fibre_disk_OBD
  cbase_compact := C.edge_cbase_compact_OBD P geom
  cbase_domain := P.edge_cbase_domain_OBD hι (C.edge_cbase_compact_OBD P geom) geom

end BoundaryGaf02ChainE

end EdgeCutFacts

end DifferentialGeometry.Geometry.Collapse
