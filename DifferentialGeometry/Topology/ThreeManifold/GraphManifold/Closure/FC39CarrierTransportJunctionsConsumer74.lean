import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportTubes74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersLabelled
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointJunctions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonRows

/-!
# Draft 74, D74-6: consumers of the junction / tube transport (real inhabitants)

Lane C14-REG-CHAIN (by S-REG-CHAIN), G23 (consumer). The transport `JunctionsV2.mapCarrier74` /
`LabelledCornerTubes.mapCarrier74` is applied along the identity carrier diffeomorphism to two
compiled inhabitants of the tree:

* the S³ configuration (`sphereJunctions`, `sphereLabelledTubes sphereJunctions`: four registered
  corners, a non-vacuous inhabitant of both records);
* the one-piece configuration (`X136.configurationJunctions b`, `X136.configurationTubes b`:
  empty edge ends).

The transported S³ records keep the four corners and the rim base points.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- The identity carrier diffeomorphism of the S³ carrier. -/
def sphereRefl74 : sphereW.Carrier ≃ₘ⟮sphereW.model, sphereW.model⟯ sphereW.Carrier :=
  Diffeomorph.refl sphereW.model sphereW.Carrier ∞

/-- The S³ junctions transported along the identity. -/
def sphereJunctionsTransported74 :=
  sphereJunctions.mapCarrier74 sphereRefl74 rfl

/-- The S³ labelled corner tubes transported along the identity. -/
def sphereTubesTransported74 : LabelledCornerTubes sphereJunctionsTransported74 :=
  (sphereLabelledTubes sphereJunctions).mapCarrier74 sphereRefl74 rfl

/-- The transported S³ junctions have the four registered corners. -/
theorem sphereJunctionsTransported74_card :
    Nat.card (sphereEdgeBundle.mapCarrier74 sphereRefl74 rfl).EdgeEnd = 4 := by
  change Nat.card sphereEdgeBundle.EdgeEnd = 4
  rw [← Nat.card_congr sphereEdgeModels.endpointEquiv]
  change Nat.card (Fin 2 × Bool) = 4
  simp

/-- The rim base points of the transported junctions are the original ones. -/
theorem sphereJunctionsTransported74_rimBase :
    sphereJunctionsTransported74.rimBase = sphereJunctions.rimBase :=
  rfl

/-- The transported S³ tube neighbourhoods are the original ones. -/
theorem sphereTubesTransported74_base
    (x : (sphereEdgeBundle.mapCarrier74 sphereRefl74 rfl).EdgeEnd) :
    sphereTubesTransported74.base x = (sphereLabelledTubes sphereJunctions).base x :=
  rfl

/-- The transported tube of an endpoint of the S³ configuration is the identity image of the
original tube. -/
theorem sphereTubesTransported74_tube
    (x : (sphereEdgeBundle.mapCarrier74 sphereRefl74 rfl).EdgeEnd) :
    sphereTubesTransported74.tube x =
      sphereRefl74 '' (sphereLabelledTubes sphereJunctions).tube x :=
  CircleBundle.mapCarrier74_tube sphereRefl74 sphereCircleBundle _

/-- The one-piece configuration's junctions and tubes transported along the identity. -/
def configurationJunctionsTransported74 (b : Bool) :=
  (X136.configurationJunctions b).mapCarrier74
    (Diffeomorph.refl (X136.configurationW b).model (X136.configurationW b).Carrier ∞) rfl

/-- The one-piece configuration's labelled corner tubes transported along the identity. -/
def configurationTubesTransported74 (b : Bool) :
    LabelledCornerTubes (configurationJunctionsTransported74 b) :=
  (X136.configurationTubes b).mapCarrier74
    (Diffeomorph.refl (X136.configurationW b).model (X136.configurationW b).Carrier ∞) rfl

end GC.GraphManifold.Assembly.FC39P0
