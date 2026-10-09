import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportRows74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportJunctionsConsumer74

/-!
# Draft 74, D74-6: consumers of `FC39RowsV2.transport74` (real inhabitants)

Lane C14-REG-CHAIN (by S-REG-CHAIN), G24 (consumer). The record-level transport is applied along
the identity carrier diffeomorphism to the compiled row records of the tree: the S³ rows
(`sphereRowsOf sphereJunctions`, four registered corners; a non-vacuous inhabitant of every field)
and the one-piece rows (`X136.configurationRows b`, empty edge ends).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- The S³ rows transported along the identity carrier diffeomorphism. -/
def sphereRowsTransported74 :
    FC39RowsV2 sphereW ((BoundaryTori.empty sphereW).transport74 sphereRefl74) :=
  (sphereRowsOf sphereJunctions).transport74 sphereRefl74 rfl

/-- The transported S³ rows have the four registered corners. -/
theorem sphereRowsTransported74_card :
    Nat.card sphereRowsTransported74.edge.EdgeEnd = 4 :=
  sphereJunctionsTransported74_card

/-- The transported S³ rows have the transported circle region `M₃ = e(M₃)` (the identity
image). -/
theorem sphereRowsTransported74_region :
    sphereRowsTransported74.circle.region =
      sphereRefl74 '' (sphereRowsOf sphereJunctions).circle.region :=
  ((sphereRowsOf sphereJunctions).transport74_sets sphereRefl74 rfl).2.2.2.1

/-- The one-piece rows transported along the identity carrier diffeomorphism. -/
def configurationRowsTransported74 (b : Bool) :
    FC39RowsV2 (X136.configurationW b)
      ((BoundaryTori.empty (X136.configurationW b)).transport74
        (Diffeomorph.refl (X136.configurationW b).model (X136.configurationW b).Carrier ∞)) :=
  (X136.configurationRows b).transport74
    (Diffeomorph.refl (X136.configurationW b).model (X136.configurationW b).Carrier ∞) rfl

end GC.GraphManifold.Assembly.FC39P0
