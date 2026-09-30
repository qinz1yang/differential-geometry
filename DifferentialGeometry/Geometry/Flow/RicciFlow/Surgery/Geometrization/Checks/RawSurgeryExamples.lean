import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open GC.Interface
universe u

namespace GC.TeamChecks

def initial_marking (P : OrientedThreeStage.{u}) (g : P.Metric)
    (b : ℝ) (hb : 0 ≤ b) :
    InitialIdentification P g ((RawSurgery.ofInitial P g).observation.observe b hb) :=
  (RawSurgery.ofInitial P g).initial b hb

theorem locally_finite (P : OrientedThreeStage.{u}) (g : P.Metric) (a b : ℝ) :
    ((RawSurgery.ofInitial P g).observation.eventTimes ∩ Icc a b).Finite :=
  (RawSurgery.ofInitial P g).finite_events a b

theorem event_geometry (P : OrientedThreeStage.{u}) (g : P.Metric) (n : ℕ)
    (i : Fin ((RawSurgery.ofInitial P g).tower.history n).eventCount) :
    GC.Surgery.ActualMetricEventGeometry
      (((RawSurgery.ofInitial P g).tower.history n).coreEvent i).toMetricCutCapEvent :=
  (RawSurgery.ofInitial P g).event_geometry n i

end GC.TeamChecks
