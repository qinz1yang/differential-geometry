import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.CappingRealization
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_poincareControlled
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : SmoothCutCapCompletion X)
    (hD : ∀ c : ConnectedComponents D.Carrier,
      DifferentialGeometry.Topology.isStandardConnectedSum
        (D.component c).Carrier) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition X h).poincareControlled := hD

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
