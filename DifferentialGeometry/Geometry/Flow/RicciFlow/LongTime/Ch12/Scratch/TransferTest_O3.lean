import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)

def sliceIndex_O3 (s : RegularSlice F.observation) : ℕ := Nat.ceil s.time

def sliceTime_O3 (s : RegularSlice F.observation) :
    Icc (0 : ℝ) (F.tower.history (sliceIndex_O3 F s)).toHistory.horizon :=
  ⟨s.time, s.positive.le, by
    change s.time ≤ (F.tower.history (sliceIndex_O3 F s)).horizon
    rw [F.tower.horizon_eq]; exact Nat.le_ceil _⟩

def sliceStage_O3 (s : RegularSlice F.observation) :
    Fin ((F.tower.history (sliceIndex_O3 F s)).eventCount + 1) :=
  (F.tower.history (sliceIndex_O3 F s)).toHistory.activeStage (sliceTime_O3 F s)

theorem slice_preceding_O3 (s : RegularSlice F.observation) :
    (F.tower.history (sliceIndex_O3 F s)).time (sliceStage_O3 F s) < s.time :=
  s.preceding

def sliceHistory_O3 (s : RegularSlice F.observation) : RetainedCoreHistory.{u} :=
  (F.tower.history (sliceIndex_O3 F s)).prefixAt (sliceStage_O3 F s)

def sliceSlab_O3 (s : RegularSlice F.observation) :
    ((sliceHistory_O3 F s).stage (Fin.last (sliceHistory_O3 F s).eventCount)).ClosedSlab
      ((sliceHistory_O3 F s).time (Fin.last (sliceHistory_O3 F s).eventCount)) s.time :=
  (F.tower.history (sliceIndex_O3 F s)).toHistory.closedPrefixAt (sliceTime_O3 F s)
    (slice_preceding_O3 F s)

example (s : RegularSlice F.observation) :
    (sliceHistory_O3 F s).stage (Fin.last (sliceHistory_O3 F s).eventCount) = s.stage := rfl

example (s : RegularSlice F.observation) :
    (sliceSlab_O3 F s).flow.base.metric s.time = s.metric := by
  unfold RegularSlice.metric ObservedHistory.stageMetric
  simp only [Fin.lastCases_last]
  have h : s.history.time (Fin.last s.history.eventCount) < s.history.horizon := s.preceding
  rw [dite_cond_eq_true (eq_true h)]
  rfl

end GC.LongTime.Ch12
