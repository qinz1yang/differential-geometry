import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Cutoff.UniformDebit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.CanonicalNeighborhood.ThroughSurgery

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
theorem exists_poincare_controlled_extinction
    (M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3)
    [SimplyConnectedSpace M.Carrier]
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    Nonempty (PoincareControlledExtinction M g) := by
  have : SimplyConnectedSpace (M).Carrier :=
    inferInstanceAs (SimplyConnectedSpace M.Carrier)
  exact exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong
    (M) g
    (uniform_debit_surgery_step (M) g)
    (canonical_neighborhoods_through_surgery (M) g)

end DifferentialGeometry.PDE.RicciFlow.Surgery

end
