import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutFoldCompare
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawConnectedSumConnector
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport

/-!
# Consumer of A6: the closed separating sphere step through the fixed connected-sum endpoint

`SphereCutCapped.exists_rawGraphPresentation_of_closedSeparating`: for a connected carrier `W`
without boundary tori cut along a separating sphere seam whose two capped components are closed, raw
graph presentations of the two components give one of `W`. Wiring of external review 38: each
component's presentation is carried to its closed model (B0) by an actual diffeomorphism, the fixed
endpoint `rawGraphPresentation_connectedSum` gives the presentation of the fixed `connectedSum`, and
A6 (`compare_closedSeparating`) is the actual diffeomorphism onto `W`
(`nonempty_rawGraphPresentation_of_carrierDiffeomorph`). No fold hypothesis is supplied.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **The closed separating sphere step.** -/
theorem SphereCutCapped.exists_rawGraphPresentation_of_closedSeparating (W : CompactCarrier.{u})
    [ConnectedSpace W.Carrier] {S : SphereSeam W} {E : BoundaryTori W 0}
    (X : SphereCutCapped W S E) (DQ : X.Q.Components) (h2 : DQ.count = 2)
    (hQ : ∀ i, (GC.Topology.componentCarrier X.Q DQ i).model.boundary
      (GC.Topology.componentCarrier X.Q DQ i).Carrier = ∅)
    (R : ∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) :
    Nonempty (RawGraphPresentation W) := by
  have hc : ∀ i, PreconnectedSpace (GC.Topology.componentCarrier X.Q DQ i).Carrier := fun i =>
    (DQ.connected i).toPreconnectedSpace
  have hG : ∀ i, Nonempty (RawGraphPresentation (NoCuts.carrier
      (@boundaryEmptyClosedModel (GC.Topology.componentCarrier X.Q DQ i) (hQ i) (DQ.connected i)))) :=
    fun i => @nonempty_rawGraphPresentation_of_carrierDiffeomorph _ _ (hc i) (R i)
      (@boundaryEmptyClosedDiffeomorph _ (hQ i) (DQ.connected i))
  obtain ⟨G0⟩ := hG (Fin.cast h2.symm 0)
  obtain ⟨G1⟩ := hG (Fin.cast h2.symm 1)
  obtain ⟨Gsum⟩ := rawGraphPresentation_connectedSum _ _ G0 G1
  obtain ⟨e⟩ := compare_closedSeparating W X DQ h2 hQ
  exact nonempty_rawGraphPresentation_of_carrierDiffeomorph Gsum e

end GC.GraphManifold.Assembly
