import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GGlobalFacesExist
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereGlobalFacesV2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceSphere

/-!
# FC39 GROUP G: the general global face functions V2 on the S³ rows (consumer)

Lane FC39-G-GFF(b), F6 consumer. The general existence theorem `exists_globalFaceFunctions_GGFF`
applied to the wide S³ rows `sphereRowsW sphereJunctions` (four actual faces, four registered
corners), next to the hand-made forgetful instance `sphereGlobalFacesV2_GGFF` of G1:

* `sphere_exists_globalFaceFunctionsV2_GGFF` — the general theorem at S³;
* `sphere_exists_preparedV2_GGFF` — prepared rows V2 over the S³ rows from the general theorem;
* `sphere_generalGlobalFaces_card_GGFF` — the general output has exactly four faces (its face type
  is the actual face type of the rows, `Nat.card = 4`, `sphere_circleFace_card_GTR`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- The general existence theorem of the global face functions V2 at the S³ rows. -/
theorem sphere_exists_globalFaceFunctionsV2_GGFF :
    Nonempty (GlobalFaceFunctionsV2 (sphereRowsW sphereJunctions)) :=
  exists_globalFaceFunctions_GGFF (sphereRowsW sphereJunctions)

/-- Prepared rows V2 over the S³ rows, from the general theorem. -/
theorem sphere_exists_preparedV2_GGFF :
    ∃ Pr : FC39PreparedV2 sphereW (BoundaryTori.empty sphereW), Pr.rows = sphereRowsW sphereJunctions :=
  exists_preparedV2_GGFF (sphereRowsW sphereJunctions)

/-- The general output at S³ has exactly four faces (one per actual face of the rows). -/
theorem sphere_generalGlobalFaces_card_GGFF :
    Nat.card sphere_exists_globalFaceFunctionsV2_GGFF.some.Face = 4 :=
  (Nat.card_congr sphere_exists_globalFaceFunctionsV2_GGFF.some.actualFace).trans
    sphere_circleFace_card_GTR

end GC.GraphManifold.Assembly.FC39P0
