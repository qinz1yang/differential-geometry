import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageTubes74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSphereInhabitant74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLoopInhabitant74

/-!
# Draft 74, package J0 consumer: junctions and labelled corner tubes on the S³ singleton and the
`S² × S¹` loop

Lane S-JUNCTIONS (suffix `_JN74`). `junctions_of_actual_decomposition74` and
`labelledCornerTubes_of_actual_decomposition74` applied to the stage geometry of the closed S³
singleton (whole zero domain) and of the closed slim loop `S² × S¹`; the cover of each is the
FDC04 cover of its single piece, and the corner tubes live over an empty family of endpoints.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

/-- **J0 consumer**: the junctions of the S³ singleton. -/
def sphereJunctions74 :=
  junctions_of_actual_decomposition74 sphereStageGeometry74 sphereCutChoice74 sphereCutGeometry74

/-- **J0 consumer**: the labelled corner tubes of the S³ singleton. -/
def sphereTubes74 : LabelledCornerTubes sphereJunctions74 :=
  labelledCornerTubes_of_actual_decomposition74 sphereStageGeometry74 sphereCutChoice74
    sphereCutGeometry74

/-- **J0 consumer**: the junctions of the `S² × S¹` loop. -/
def slimLoopJunctions74 :=
  junctions_of_actual_decomposition74 slimLoopStageGeometry74 slimLoopCutChoice74
    slimLoopCutGeometry74

/-- **J0 consumer**: the labelled corner tubes of the `S² × S¹` loop. -/
def slimLoopTubes74 : LabelledCornerTubes slimLoopJunctions74 :=
  labelledCornerTubes_of_actual_decomposition74 slimLoopStageGeometry74 slimLoopCutChoice74
    slimLoopCutGeometry74

/-- The pieces of the S³ singleton cover `W` through the cover of the junctions. -/
theorem sphereJunctions74_cover : (⋃ a, allPieces sphereCutGeometry74.rows.slimPieces
    sphereCutGeometry74.rows.edge sphereCutGeometry74.rows.circle a) = univ :=
  sphereJunctions74.cover

/-- The pieces of the `S² × S¹` loop cover `W` through the cover of the junctions. -/
theorem slimLoopJunctions74_cover : (⋃ a, allPieces slimLoopCutGeometry74.rows.slimPieces
    slimLoopCutGeometry74.rows.edge slimLoopCutGeometry74.rows.circle a) = univ :=
  slimLoopJunctions74.cover

end GC.GraphManifold.Assembly.FC39P0.X136
