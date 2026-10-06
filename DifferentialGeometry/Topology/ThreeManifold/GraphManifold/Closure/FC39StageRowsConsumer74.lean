import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRows74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSphereInhabitant74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLoopInhabitant74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed

/-!
# Draft 74, package J1 consumer: the assembled rows of the S³ singleton and the `S² × S¹` loop
feed `exists_strongCertificate_of_rows_GFIN`

Lane S-JUNCTIONS (suffix `_JN74`). `rows_of_smooth_stage_geometry74` on the stage geometry of the
closed S³ singleton (whole zero domain, empty slim / edge / circle) and of the closed slim loop
`S² × S¹` (one `overCircle` slim piece over the whole circle component, `K₃ = D₃ = S¹`): the
assembled rows satisfy the abstract link (`StageRowsLink74`) and the end-to-end consumer
`exists_strongCertificate_of_rows_GFIN` accepts them. Regressions of the contracts (D74-19), not
the completion criterion.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

/-- **J1 consumer**: the assembled S³ rows. -/
def sphereRows74 : FC39RowsV2 zeroW (BoundaryTori.empty zeroW) :=
  rowsOfStageGeometry74 sphereStageGeometry74 sphereCutChoice74 sphereCutGeometry74

/-- The assembled S³ rows have the whole zero domain of `A` and the empty edge piece and region. -/
theorem sphereRows74_link :
    sphereRows74.zero = zeroDomains ∧ sphereRows74.edge.edgePiece = ∅ ∧
      sphereRows74.circle.region = ∅ :=
  let L := rowsOfStageGeometry74_link sphereStageGeometry74 sphereCutChoice74 sphereCutGeometry74
  ⟨L.zeroSlim.zero_eq,
    L.edge.edge_piece.trans
      (slimOnly74_edgeSet zeroDomains zeroCusps (SlimStage74.empty zeroW) sphereCutChoice74),
    L.circle.circle_region.trans
      (slimOnly74_circleRegion zeroDomains zeroCusps (SlimStage74.empty zeroW) sphereCutChoice74)⟩

/-- **The end-to-end consumer**: the assembled S³ rows feed
`exists_strongCertificate_of_rows_GFIN`. -/
theorem sphereStage_strongCertificate_74 :
    Nonempty (StrongCertificate zeroW (BoundaryTori.empty zeroW)) :=
  exists_strongCertificate_of_rows_GFIN sphereRows74

/-- **J1 consumer**: the assembled rows of the `S² × S¹` loop. -/
def slimLoopRows74 : FC39RowsV2 slimWc (BoundaryTori.empty slimWc) :=
  rowsOfStageGeometry74 slimLoopStageGeometry74 slimLoopCutChoice74 slimLoopCutGeometry74

/-- The assembled loop rows have the one slim piece filling `S² × S¹` and empty edge and circle
pieces. -/
theorem slimLoopRows74_link : slimLoopRows74.slim.count = 1 ∧ slimLoopRows74.slim.union = univ ∧
    slimLoopRows74.edge.edgePiece = ∅ ∧ slimLoopRows74.circle.region = ∅ :=
  let L := rowsOfStageGeometry74_link slimLoopStageGeometry74 slimLoopCutChoice74
    slimLoopCutGeometry74
  ⟨rfl, L.zeroSlim.slim_union.trans slimLoopCutChoice74_slimSet,
    L.edge.edge_piece.trans (slimOnly74_edgeSet slimZero slimCusps slimLoopStage74
      slimLoopCutChoice74),
    L.circle.circle_region.trans (slimOnly74_circleRegion slimZero slimCusps slimLoopStage74
      slimLoopCutChoice74)⟩

/-- **The end-to-end consumer**: the assembled `S² × S¹` rows feed
`exists_strongCertificate_of_rows_GFIN`. -/
theorem slimLoopStage_strongCertificate_74 :
    Nonempty (StrongCertificate slimWc (BoundaryTori.empty slimWc)) :=
  exists_strongCertificate_of_rows_GFIN slimLoopRows74

end GC.GraphManifold.Assembly.FC39P0.X136
