import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.closedSlabRestart
    (H : RetainedCoreHistory.{u}) (T : ℝ)
    (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab
      (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hcompat : H.extendHorizonCompatible T S) :
    ∃ H' : RetainedCoreHistory.{u},
      H'.horizon = T ∧ H.toHistory.IsPrefixOf H'.toHistory := by
  let H' := H.extendHorizon T hT S hS
  have hp := H.extendHorizon_isPrefixOf T hT S hS hcompat
  have hh : H'.horizon = T := H.toHistory_extendHorizon_horizon T hT S hS
  exact ⟨H', hh, hp⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
