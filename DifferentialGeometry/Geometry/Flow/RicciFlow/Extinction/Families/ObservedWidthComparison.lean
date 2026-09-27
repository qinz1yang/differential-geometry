import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.HistoryWidthJumpComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ActualWidthDeformation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedWidthDini
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerWidthExtinction

noncomputable section

open Set Filter
open Bundle Manifold
open scoped Topology ENNReal Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open DifferentialGeometry.PDE.RicciFlow.Extinction.Width (ChildComparisonData)

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem observedHistoryWidthValue_upperRightDiniLE_of_rampDeformation
    (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c : ℝ} (hc : 0 < c) (hscalar : HistoryScalarLowerBound H c)
    (hinc : ∀ (i : Fin H.eventCount)
      (p : ConnectedComponents (H.stage i.castSucc).Carrier)
      (_hSC : SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier),
      ComponentInteriorRampDeformation (H.stage i.castSucc) (H.time i.castSucc)
        (H.time i.succ) (H.event i).incoming.lt p)
    (hclosed : ∀ (hfin : H.time (Fin.last H.eventCount) < H.horizon)
      (p : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
      (_hSC : SimplyConnectedSpace
        ((H.stage (Fin.last H.eventCount)).component p).Carrier),
      ComponentInteriorRampDeformation (H.stage (Fin.last H.eventCount))
        (H.time (Fin.last H.eventCount)) H.horizon (H.finalSlab hfin).lt p) :
    ∀ t ∈ Ico (0 : ℝ) H.horizon, t ∉ H.eventTimes →
      UpperRightDiniLE (observedHistoryWidthValue H h0 terminal) t
        (-2 * Real.pi + 3 * observedHistoryWidthValue H h0 terminal t / (4 * (t + c))) :=
  observedHistoryWidthValue_upperRightDiniLE_of_slabIncrementBounds H h0 terminal hc hscalar
    (fun i p hSC => incoming_component_incrementBound_of_rampFamilyDeformation
      (H.event i).incoming p hSC (hinc i p hSC))
    (fun hfin p hSC => closed_component_incrementBound_of_rampFamilyDeformation
      (H.finalSlab hfin) p hSC (hclosed hfin p hSC))

theorem observedComparisonRecord_of_childComparison (H : ObservedHistory.{u})
    (parameters : CutoffParameters)
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c A : ℝ} (hc : 0 < c) (hHpos : 0 < H.horizon)
    (hinitial : Extinction.Width.historyWidth H h0 terminal
      (Extinction.Width.historyStageTime H 0) ≤ A)
    (hchild : ∀ i : Fin H.eventCount, ChildComparisonData (cutoff i))
    (hdini : ∀ t ∈ Ico (0 : ℝ) H.horizon, t ∉ H.eventTimes →
      UpperRightDiniLE (observedHistoryWidthValue H h0 terminal) t
        (-2 * Real.pi + 3 * observedHistoryWidthValue H h0 terminal t / (4 * (t + c)))) :
    Nonempty (ObservedComparisonRecord H c A) :=
  observedComparisonRecord_of_historyWidth H h0 terminal hc hHpos hinitial
    (fun t ht => observedHistoryWidthValue_not_event_continuousAt H h0 terminal t ht)
    (fun i hi => Extinction.Width.historyWidth_rightContinuousAt_event H h0 terminal i hi)
    (fun i => Extinction.Width.historyWidth_event_jump_of_childComparison H parameters cutoff
      h0 terminal i (hchild i))
    hdini

theorem observedComparisonRecord_of_childComparison_of_rampDeformation
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c A : ℝ} (hc : 0 < c) (hHpos : 0 < H.horizon)
    (hscalar : HistoryScalarLowerBound H c)
    (hinitial : Extinction.Width.historyWidth H h0 terminal
      (Extinction.Width.historyStageTime H 0) ≤ A)
    (hchild : ∀ i : Fin H.eventCount, ChildComparisonData (cutoff i))
    (hinc : ∀ (i : Fin H.eventCount)
      (p : ConnectedComponents (H.stage i.castSucc).Carrier)
      (_hSC : SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier),
      ComponentInteriorRampDeformation (H.stage i.castSucc) (H.time i.castSucc)
        (H.time i.succ) (H.event i).incoming.lt p)
    (hclosed : ∀ (hfin : H.time (Fin.last H.eventCount) < H.horizon)
      (p : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
      (_hSC : SimplyConnectedSpace
        ((H.stage (Fin.last H.eventCount)).component p).Carrier),
      ComponentInteriorRampDeformation (H.stage (Fin.last H.eventCount))
        (H.time (Fin.last H.eventCount)) H.horizon (H.finalSlab hfin).lt p) :
    Nonempty (ObservedComparisonRecord H c A) :=
  observedComparisonRecord_of_childComparison H parameters cutoff h0 terminal hc hHpos hinitial
    hchild
    (observedHistoryWidthValue_upperRightDiniLE_of_rampDeformation H h0 terminal hc hscalar
      hinc hclosed)

theorem ObservationTower.uniformRecordsAbove_of_childComparison_of_rampDeformation
    (T : ObservationTower P g) {c A : ℝ} (hc : 0 < c)
    (hdata : ∀ (b : ℝ) (hb : 0 < b) (_hlt : extinctionThreshold c A < b)
      (terminal : ConnectedComponents ((T.observe b hb.le).stage
        (Fin.last (T.observe b hb.le).eventCount)).Carrier),
      ∃ (parameters : CutoffParameters)
        (cutoff : ∀ i : Fin (T.observe b hb.le).eventCount,
          GeometricCutoffRecord (T.observe b hb.le) i parameters)
        (h0 : ∀ p : ConnectedComponents ((T.observe b hb.le).stage 0).Carrier,
          SimplyConnectedSpace (((T.observe b hb.le).stage 0).component p).Carrier),
        HistoryScalarLowerBound (T.observe b hb.le) c ∧
        (Extinction.Width.historyWidth (T.observe b hb.le) h0 terminal
          (Extinction.Width.historyStageTime (T.observe b hb.le) 0) ≤ A) ∧
        (∀ i : Fin (T.observe b hb.le).eventCount, ChildComparisonData (cutoff i)) ∧
        (∀ (i : Fin (T.observe b hb.le).eventCount)
          (p : ConnectedComponents ((T.observe b hb.le).stage i.castSucc).Carrier)
          (_hSC : SimplyConnectedSpace
            (((T.observe b hb.le).stage i.castSucc).component p).Carrier),
          ComponentInteriorRampDeformation ((T.observe b hb.le).stage i.castSucc)
            ((T.observe b hb.le).time i.castSucc) ((T.observe b hb.le).time i.succ)
            ((T.observe b hb.le).event i).incoming.lt p) ∧
        ∀ (hfin : (T.observe b hb.le).time (Fin.last (T.observe b hb.le).eventCount) <
            (T.observe b hb.le).horizon)
          (p : ConnectedComponents ((T.observe b hb.le).stage
            (Fin.last (T.observe b hb.le).eventCount)).Carrier)
          (_hSC : SimplyConnectedSpace (((T.observe b hb.le).stage
            (Fin.last (T.observe b hb.le).eventCount)).component p).Carrier),
          ComponentInteriorRampDeformation ((T.observe b hb.le).stage
            (Fin.last (T.observe b hb.le).eventCount))
            ((T.observe b hb.le).time (Fin.last (T.observe b hb.le).eventCount))
            (T.observe b hb.le).horizon ((T.observe b hb.le).finalSlab hfin).lt p) :
    T.UniformRecordsAbove c A := by
  intro b hb hlt terminal
  obtain ⟨parameters, cutoff, h0, hscalar, hinitial, hchild, hinc, hclosed⟩ :=
    hdata b hb hlt terminal
  exact observedComparisonRecord_of_childComparison_of_rampDeformation (T.observe b hb.le)
    parameters cutoff h0 terminal (c := c) (A := A) hc (by simpa using hb)
    hscalar hinitial hchild hinc hclosed

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
