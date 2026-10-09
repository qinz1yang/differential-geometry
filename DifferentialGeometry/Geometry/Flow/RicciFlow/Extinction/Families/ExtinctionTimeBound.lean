import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedWidthDini
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.SlabScalarLowerBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerWidthExtinction

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open DifferentialGeometry.PDE.RicciFlow.Extinction.Width

universe u

namespace ObservedHistory

theorem exists_observedComparisonRecord_of_historyWidth (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (parameters : CutoffParameters)
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hscalar : HistoryScalarLowerBound H c)
    (hinitial : historyWidth H h0 terminal (historyStageTime H 0) ≤ A)
    (hthr : extinctionThreshold c A < H.horizon) :
    Nonempty (ObservedComparisonRecord H c A) :=
  observedComparisonRecord_of_historyWidth_of_scalarLowerBound H h0 terminal hc
    ((extinctionThreshold_nonneg hc hA).trans_lt hthr) hscalar hinitial
    (fun t ht => historyWidth_continuousAt_of_not_event H h0 terminal t fun i hi => ht ⟨i, hi.symm⟩)
    (fun i hi => historyWidth_rightContinuousAt_event H h0 terminal i hi)
    (fun i => historyWidth_event_jump H parameters cutoff h0 terminal i)

theorem isExtinctAtHorizon_of_historyWidth (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (parameters : CutoffParameters)
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hscalar : HistoryScalarLowerBound H c)
    (hinitial : ∀ terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier,
      historyWidth H h0 terminal (historyStageTime H 0) ≤ A)
    (hthr : extinctionThreshold c A < H.horizon) :
    H.IsExtinctAtHorizon :=
  H.final_empty_of_uniform_records hthr fun terminal =>
    exists_observedComparisonRecord_of_historyWidth H h0 parameters cutoff terminal hc hA hscalar
      (hinitial terminal) hthr

theorem not_nonempty_observedComparisonRecord_atZero (P : OrientedThreeStage.{u}) (g : P.Metric)
    {c A : ℝ} :
    ¬ Nonempty (ObservedComparisonRecord (atZero P g) c A) :=
  fun h => (lt_irrefl (0 : ℝ)) h.some.hypotheses.horizon_pos

end ObservedHistory

namespace ObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem uniformRecordsAbove_of_historyWidth (T : ObservationTower P g)
    (h0 : ∀ (b : ℝ) (hb : 0 < b),
      ∀ c : ConnectedComponents ((T.observe b hb.le).stage 0).Carrier,
        SimplyConnectedSpace (((T.observe b hb.le).stage 0).component c).Carrier)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.observe b hb.le) i (parameters b))
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hscalar : ∀ (b : ℝ) (hb : 0 < b), HistoryScalarLowerBound (T.observe b hb.le) c)
    (hinitial : ∀ (b : ℝ) (hb : 0 < b),
      ∀ terminal : ConnectedComponents ((T.observe b hb.le).stage
        (Fin.last (T.observe b hb.le).eventCount)).Carrier,
      historyWidth (T.observe b hb.le) (h0 b hb) terminal
        (historyStageTime (T.observe b hb.le) 0) ≤ A) :
    T.UniformRecordsAbove c A :=
  fun b hb hlt terminal =>
    ObservedHistory.exists_observedComparisonRecord_of_historyWidth (T.observe b hb.le) (h0 b hb)
      (parameters b) (cutoff b hb) terminal hc hA (hscalar b hb) (hinitial b hb terminal) hlt

theorem towerExtinct_of_historyWidth (T : ObservationTower P g)
    (h0 : ∀ (b : ℝ) (hb : 0 < b),
      ∀ c : ConnectedComponents ((T.observe b hb.le).stage 0).Carrier,
        SimplyConnectedSpace (((T.observe b hb.le).stage 0).component c).Carrier)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.observe b hb.le) i (parameters b))
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hscalar : ∀ (b : ℝ) (hb : 0 < b), HistoryScalarLowerBound (T.observe b hb.le) c)
    (hinitial : ∀ (b : ℝ) (hb : 0 < b),
      ∀ terminal : ConnectedComponents ((T.observe b hb.le).stage
        (Fin.last (T.observe b hb.le).eventCount)).Carrier,
      historyWidth (T.observe b hb.le) (h0 b hb) terminal
        (historyStageTime (T.observe b hb.le) 0) ≤ A) :
    towerExtinct T :=
  T.towerExtinct_of_uniformRecordsAbove
    (T.uniformRecordsAbove_of_historyWidth h0 parameters cutoff hc hA hscalar hinitial)

theorem observe_le_extinctionThreshold_of_nonempty (T : ObservationTower P g) {c A : ℝ}
    (hrec : T.UniformRecordsAbove c A) {b : ℝ} (hb : 0 < b)
    (hne : Nonempty ((T.observe b hb.le).stage
      (Fin.last (T.observe b hb.le).eventCount)).Carrier) :
    b ≤ extinctionThreshold c A :=
  le_of_not_gt fun hlt =>
    ((T.records_iff_final_empty_of_threshold_lt b hb.le hlt).mp (hrec b hb hlt)).false
      hne.some

theorem uniformRecordsAbove_of_scalarLowerBound
    {P : OrientedThreeStage.{u}} [ConnectedSpace P.Carrier] [SimplyConnectedSpace P.Carrier]
    {g : P.Metric} (T : ObservationTower P g)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.observe b hb.le) i (parameters b))
    {c : ℝ} (hc : 0 < c)
    (hscalar : ∀ (b : ℝ) (hb : 0 < b), HistoryScalarLowerBound (T.observe b hb.le) c) :
    ∃ Γ₀ : RegularRepresentative (I := ThreeModel) (positiveFreeContractibleClass P.orientation),
      T.UniformRecordsAbove c (familyMaximum g Γ₀.1) := by
  obtain ⟨Γ₀, hbound, _hscale, hhistory⟩ := rfs_initial_width_data P g
  refine ⟨Γ₀, ?_⟩
  refine T.uniformRecordsAbove_of_historyWidth
    (fun b hb => initialIdentification_components_simplyConnected P g (T.observe b hb.le)
      (T.observeInitial b hb.le))
    parameters cutoff hc (hbound.1.trans hbound.2.1) hscalar ?_
  intro b hb terminal
  exact (hhistory (T.observe b hb.le) (T.observeInitial b hb.le) (parameters b)
    (cutoff b hb) terminal).2.1

theorem uniformRecordsAbove_of_initialScalarLowerBound
    {P : OrientedThreeStage.{u}} [ConnectedSpace P.Carrier] [SimplyConnectedSpace P.Carrier]
    {g : P.Metric} (T : ObservationTower P g)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.observe b hb.le) i (parameters b))
    {c : ℝ} (hc : 0 < c)
    (hscalar0 : ∀ (b : ℝ) (hb : 0 < b),
      ∀ y : ((T.observe b hb.le).stage 0).Carrier,
        -3 / (2 * ((T.observe b hb.le).time 0 + c)) ≤
          DifferentialGeometry.Geometry.Curvature.metricScalarAt
            ((T.observe b hb.le).initialMetric 0) y) :
    ∃ Γ₀ : RegularRepresentative (I := ThreeModel) (positiveFreeContractibleClass P.orientation),
      T.UniformRecordsAbove c (familyMaximum g Γ₀.1) :=
  T.uniformRecordsAbove_of_scalarLowerBound parameters cutoff hc fun b hb =>
    (DifferentialGeometry.PDE.RicciFlow.historyScalarLowerBound_of_history
      (cutoff b hb) hc (hscalar0 b hb)).1

theorem towerExtinct_of_initialScalarLowerBound
    {P : OrientedThreeStage.{u}} [ConnectedSpace P.Carrier] [SimplyConnectedSpace P.Carrier]
    {g : P.Metric} (T : ObservationTower P g)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.observe b hb.le) i (parameters b))
    {c : ℝ} (hc : 0 < c)
    (hscalar0 : ∀ (b : ℝ) (hb : 0 < b),
      ∀ y : ((T.observe b hb.le).stage 0).Carrier,
        -3 / (2 * ((T.observe b hb.le).time 0 + c)) ≤
          DifferentialGeometry.Geometry.Curvature.metricScalarAt
            ((T.observe b hb.le).initialMetric 0) y) :
    towerExtinct T :=
  (T.uniformRecordsAbove_of_initialScalarLowerBound parameters cutoff hc hscalar0).elim
    fun _ h => T.towerExtinct_of_uniformRecordsAbove h

end ObservationTower

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
