import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialStageGeomJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRows74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageTubes74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed

/-!
# Draft 74, G5 consumer: the radial solid torus through J0 / J1 into GROUP G

Lane S-JUNCTIONS2 (suffix `_JN74`). The first inhabitant of the J0 / J1 contracts with a non-empty
EDGE piece (the core `h ≤ -3/4`, one circle component, no endpoint), a non-empty circle region
(`-3/4 ≤ h ≤ -1/2`), a slim band and a cusp collar: `junctions_of_actual_decomposition74` and
`labelledCornerTubes_of_actual_decomposition74` on `radialGeometry74`, the assembled rows
`rows_of_smooth_stage_geometry74` (with their `StageRowsLink74`) and
`exists_strongCertificate_of_rows_GFIN`. The edge piece and the circle region of the assembled rows
are those of the cut: `radialRows74_edgePiece`, `radialRows74_region`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

/-- **J0 on the radial solid torus**: the junctions of the cut. -/
def radialJunctions74 :=
  junctions_of_actual_decomposition74 radialStage74 radialCut74 radialGeometry74

/-- **J0 (tubes) on the radial solid torus**: vacuous (no endpoint), but assembled by R1. -/
def radialTubes74 : LabelledCornerTubes radialJunctions74 :=
  labelledCornerTubes_of_actual_decomposition74 radialStage74 radialCut74 radialGeometry74

/-- **J1 on the radial solid torus**: the assembled rows with their link to the stage data. -/
theorem radialRows74_assembled :
    ∃ Rw : FC39RowsV2 carrier boundary, StageRowsLink74 radialStage74 radialCut74 Rw :=
  rows_of_smooth_stage_geometry74 radialStage74 radialCut74 radialGeometry74

/-- The edge piece of the cut is the X135 edge core, `h ≤ -3/4`, NON-EMPTY. -/
theorem radialRows74_edgePiece :
    radialRows74.edge.edgePiece = {p : carrier.Carrier | height p ≤ -(3 / 4 : ℝ)} := by
  rw [← radial_edge_height]
  exact edgePiece_ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm radialReq74 (disjoint_empty _)

/-- The edge piece is non-empty (it contains the core circle `h = -1`). -/
theorem radialRows74_edgePiece_nonempty : radialRows74.edge.edgePiece.Nonempty := by
  rw [radialRows74_edgePiece]
  exact ⟨edgeFibreAt 1 (closedCellCenter 2), edgeCoreFibreAt_height 1 (closedCellCenter 2)⟩

/-- **Consumer**: the strong certificate of the radial solid torus from the assembled rows. -/
theorem radialStage_strongCertificate_74 : Nonempty (StrongCertificate carrier boundary) := by
  obtain ⟨Rw, -⟩ := radialRows74_assembled
  exact exists_strongCertificate_of_rows_GFIN Rw

end GC.GraphManifold.Assembly.FC39P0.X135Radial
