import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure OneStepIncoming where
  stage : OrientedThreeStage.{u}
  startTime : ℝ
  endTime : ℝ
  startTime_nonneg : 0 ≤ startTime
  startTime_lt_endTime : startTime < endTime
  slab : stage.IncomingSlab startTime endTime
  terminal : slab.TerminalLimitMetric
  singular : slab.SingularEndpoint
  parameters : CutoffParameters

namespace OneStepIncoming

def ofRecord {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) : OneStepIncoming.{u} where
  stage := H.stage i.castSucc
  startTime := H.time i.castSucc
  endTime := H.time i.succ
  startTime_nonneg := by
    simpa [H.time_zero] using H.time_strictMono.le_iff_le.mpr (Fin.zero_le i.castSucc)
  startTime_lt_endTime := H.time_strictMono i.castSucc_lt_succ
  slab := (H.event i).incoming
  terminal := (H.event i).terminal
  singular := R.singular
  parameters := p

end OneStepIncoming

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
