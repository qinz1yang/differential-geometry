import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusCornersSTR
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRows74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageTubes74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7c: the cut geometry and the strong certificate of the solid torus

`geometry_STR : StageCutGeometry74 A D` (rows, cover, faces, rims, corners of the solid torus
instance: actual ball zero domain, the X135 cusp cores, one interval edge piece whose two end disks
lie on the SAME ball sphere, the circle region), the assembled rows through
`rows_of_smooth_stage_geometry74` (with their `StageRowsLink74`) and
`exists_strongCertificate_of_rows_GFIN`. The certificate route needs no `ρ_bounds` window and no
closed-chain source: only `geometry_STR`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

/-- **`H` of the solid torus instance**: the cut geometry. -/
def geometry_STR : StageCutGeometry74 (stageGeometry_STR ballZeroDomainsL_STR)
    (cutChoice_STR ballZeroDomainsL_STR) where
  rows := rows_STR
  cover := cover_STR
  faces := faces_STR
  rims := rims_STR
  corners := corners_STR

/-- **J1 on the solid torus**: the assembled rows with their link to the stage data. -/
theorem rows_assembled_STR : ∃ Rw : FC39RowsV2 Wc X135Radial.boundary,
    StageRowsLink74 (stageGeometry_STR ballZeroDomainsL_STR)
      (cutChoice_STR ballZeroDomainsL_STR) Rw :=
  rows_of_smooth_stage_geometry74 _ _ geometry_STR

/-- **The strong certificate of the solid torus instance** from the assembled rows
(D69-11 boundary-route acceptance instance: ball zero domain, interval edge piece with two end
disks on one sphere, circle region, cusp collar). -/
theorem strongCertificate_STR : Nonempty (StrongCertificate Wc X135Radial.boundary) := by
  obtain ⟨Rw, -⟩ := rows_assembled_STR
  exact exists_strongCertificate_of_rows_GFIN Rw

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
