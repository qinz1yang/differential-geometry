import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CoherentSurgeryTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.LateOrEmpty

set_option autoImplicit false
noncomputable section

namespace GC.Interface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
universe u

structure RawSurgery (P : OrientedThreeStage.{u}) (g : P.Metric) where
  tower : RetainedCoreObservationTower P g
  event_control : ∀ n, GC.GeneralFlow.HistoryEventControl (tower.history n)

namespace RawSurgery
variable {P : OrientedThreeStage.{u}} {g : P.Metric}

def ofInitial (P : OrientedThreeStage.{u}) (g : P.Metric) : RawSurgery P g where
  tower := GC.GeneralFlow.general_retained_core_tower P g
  event_control := GC.GeneralFlow.general_retained_core_tower_control P g

abbrev observation (F : RawSurgery P g) : ObservationTower P g :=
  F.tower.toObservationTower

def initial (F : RawSurgery P g) (b : ℝ) (hb : 0 ≤ b) :
    InitialIdentification P g (F.observation.observe b hb) :=
  F.observation.observeInitial b hb

theorem finite_events (F : RawSurgery P g) (a b : ℝ) :
    (F.observation.eventTimes ∩ Icc a b).Finite :=
  F.observation.eventTimes_finite_Icc a b

theorem event_geometry (F : RawSurgery P g) (n : ℕ)
    (i : Fin (F.tower.history n).eventCount) :
    GC.Surgery.ActualMetricEventGeometry
      ((F.tower.history n).coreEvent i).toMetricCutCapEvent :=
  GC.GeneralFlow.controlled_event_geometry _ (F.event_control n i)

theorem regular_prefix (F : RawSurgery P g) (B : ℝ) :
    ∃ (t : ℝ) (ht : 0 < t), B < t ∧ t ∉ F.observation.eventTimes ∧
      (F.observation.observe t ht.le).time
        (Fin.last (F.observation.observe t ht.le).eventCount) < t ∧
      Nonempty (InitialIdentification P g (F.observation.observe t ht.le)) :=
  GC.Surgery.late_prefix_with_initial F.observation B

end RawSurgery
end GC.Interface
