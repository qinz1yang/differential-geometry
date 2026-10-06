import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportRowsCross74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportRowsConsumer74

/-!
# Draft 74, D74-6: consumers of `FC39RowsV2.transportCross74` (real inhabitants)

Lane O-CROSS, G3 (consumer). The kind-free transport agrees with the same-kind transport of lane
C14-REG-CHAIN whenever the kinds agree (`transportCross74_eq_transport74`, definitional: the two
records differ only in the proof of the whole-disk smooth embeddings), and it is applied to the
compiled S³ rows along the identity carrier diffeomorphism (four registered corners, transported
circle region), with no kind hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The kind-free transport is the same-kind transport** when the kinds agree. -/
theorem FC39RowsV2.transportCross74_eq_transport74 {W₀ W₁ : CompactCarrier.{u}} {n : ℕ}
    (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier) (hk : W₀.kind = W₁.kind)
    {E : BoundaryTori W₀ n} (Rw : FC39RowsV2 W₀ E) :
    Rw.transportCross74 e = Rw.transport74 e hk :=
  rfl

/-- The S³ rows transported along the identity carrier diffeomorphism, kind-free. -/
def sphereRowsTransportedCross74 :
    FC39RowsV2 sphereW ((BoundaryTori.empty sphereW).transport74 sphereRefl74) :=
  (sphereRowsOf sphereJunctions).transportCross74 sphereRefl74

/-- The kind-free transported S³ rows have the four registered corners. -/
theorem sphereRowsTransportedCross74_card :
    Nat.card sphereRowsTransportedCross74.edge.EdgeEnd = 4 :=
  sphereJunctionsTransported74_card

/-- The kind-free transported S³ rows have the transported circle region and `M₃` is the image. -/
theorem sphereRowsTransportedCross74_region :
    sphereRowsTransportedCross74.circle.region =
        sphereRefl74 '' (sphereRowsOf sphereJunctions).circle.region ∧
      regionM3 sphereRowsTransportedCross74.slim sphereRowsTransportedCross74.edge =
        sphereRefl74 '' regionM3 (sphereRowsOf sphereJunctions).slim
          (sphereRowsOf sphereJunctions).edge :=
  ⟨((sphereRowsOf sphereJunctions).transportCross74_sets sphereRefl74).2.2.2.1,
    ((sphereRowsOf sphereJunctions).transportCross74_sets sphereRefl74).2.2.2.2.2.2.1⟩

end GC.GraphManifold.Assembly.FC39P0
