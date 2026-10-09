import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinctionHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

def ObservationTower.UniformRecordsAbove {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (c A : ℝ) : Prop :=
  ∀ (b : ℝ) (hb : 0 < b),
    extinctionThreshold c A < b →
    ∀ _terminal : ConnectedComponents ((T.observe b hb.le).stage
      (Fin.last (T.observe b hb.le).eventCount)).Carrier,
      Nonempty (ObservedComparisonRecord (T.observe b hb.le) c A)

namespace ObservationTower

theorem uniformRecordsAbove_iff_records_above_threshold {P : OrientedThreeStage.{u}}
    {g : P.Metric} (T : ObservationTower P g) {c A : ℝ} :
    T.UniformRecordsAbove c A ↔
      ∀ (b : ℝ) (hb : 0 < b), extinctionThreshold c A < b →
        ∀ _terminal : ConnectedComponents ((T.observe b hb.le).stage
          (Fin.last (T.observe b hb.le).eventCount)).Carrier,
          Nonempty (ObservedComparisonRecord (T.observe b hb.le) c A) :=
  Iff.rfl

theorem towerExtinct_of_uniformRecordsAbove {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) {c A : ℝ} (h : T.UniformRecordsAbove c A) :
    towerExtinct T :=
  towerExtinct_of_records_above_threshold T fun b hb hlt => h b hb hlt

theorem towerExtinct_of_final_stage_isEmpty_below {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) {c A : ℝ}
    (h : IsEmpty ((T.observe (max 1 (extinctionThreshold c A + 1)) (le_trans zero_le_one
      (le_max_left 1 (extinctionThreshold c A + 1)))).stage
      (Fin.last (T.observe (max 1 (extinctionThreshold c A + 1)) (le_trans zero_le_one
        (le_max_left 1 (extinctionThreshold c A + 1)))).eventCount)).Carrier) :
    towerExtinct T :=
  ⟨max 1 (extinctionThreshold c A + 1),
    le_trans zero_le_one (le_max_left 1 (extinctionThreshold c A + 1)), h⟩

theorem uniformRecordsAbove_of_records_vacuous {P : OrientedThreeStage.{u}}
    {g : P.Metric} (T : ObservationTower P g) {c A : ℝ}
    (h : ∀ (b : ℝ) (hb : 0 < b), extinctionThreshold c A < b →
      IsEmpty ((T.observe b hb.le).stage
        (Fin.last (T.observe b hb.le).eventCount)).Carrier) :
    T.UniformRecordsAbove c A := by
  intro b hb hlt terminal
  exact False.elim ((ConnectedComponents.isEmpty_iff_isEmpty.mpr
    (show (T.observe b hb.le).IsExtinctAtHorizon from h b hb hlt)).false terminal)

end ObservationTower

theorem observedComparisonRecord_nonempty_of_hypotheses {H : ObservedHistory.{u}} {c A : ℝ}
    {W : ℝ → ℝ} (h : ScalarComparisonHypotheses c H.horizon H.eventTimes W)
    (hinit : W 0 ≤ A) :
    Nonempty (ObservedComparisonRecord H c A) :=
  ⟨{ value := W, hypotheses := h, initial_le := hinit }⟩

theorem upperRightDiniLE_linearWeight {H : ObservedHistory.{u}} {c : ℝ}
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) H.horizon) (hc : 0 < c) (hcpi : 2 * Real.pi ≤ c) :
    UpperRightDiniLE (fun s : ℝ => c * (H.horizon - s)) t
      (-2 * Real.pi + 3 * (c * (H.horizon - t)) / (4 * (t + c))) := by
  rw [upperRightDiniLE_iff_before (f := fun s : ℝ => c * (H.horizon - s)) (H := H.horizon) ht.2]
  intro eps heps
  filter_upwards [Ioc_mem_nhdsGT ht.2] with y hy _
  have hne : y - t ≠ 0 := by linarith [hy.1]
  have hslope : (c * (H.horizon - y) - c * (H.horizon - t)) / (y - t) = -c := by
    field_simp
    ring
  rw [hslope]
  have hden : 0 < 4 * (t + c) := by linarith [ht.1, hc]
  have hnum : 0 ≤ 3 * (c * (H.horizon - t)) :=
    mul_nonneg (by norm_num) (mul_nonneg hc.le (by linarith [ht.2]))
  have hfrac : 0 ≤ 3 * (c * (H.horizon - t)) / (4 * (t + c)) := div_nonneg hnum hden.le
  linarith [hcpi, heps, hfrac]

theorem observedComparisonRecordOfLinearWeight_nonempty {H : ObservedHistory.{u}} {c A : ℝ}
    (hc : 0 < c) (hcpi : 2 * Real.pi ≤ c) (hH : 0 < H.horizon) (hA : c * H.horizon ≤ A) :
    Nonempty (ObservedComparisonRecord H c A) :=
  observedComparisonRecord_nonempty_of_hypotheses
    { c_pos := hc
      horizon_pos := hH
      finite_events := ObservedHistory.eventTimes_finite H
      events_subset := ObservedHistory.eventTimes_subset_Ioc H
      nonneg := by
        intro s hs
        have hle : s ≤ H.horizon := hs.2
        have h1 : 0 ≤ H.horizon - s := by linarith
        exact mul_nonneg hc.le h1
      continuous := by
        intro s _ _
        exact (by fun_prop : ContinuousAt (fun x : ℝ => c * (H.horizon - x)) s).continuousWithinAt
      right_continuous := by
        intro s _
        exact (by fun_prop : ContinuousAt (fun x : ℝ => c * (H.horizon - x)) s).continuousWithinAt
      incoming_jump := by
        intro e he
        obtain ⟨i, rfl⟩ := he
        have hreal : ContinuousAt (fun x : ℝ => c * (H.horizon - x)) (H.time i.succ) := by
          fun_prop
        have hcont : Filter.Tendsto (fun x : ℝ => ((c * (H.horizon - x) : ℝ) : EReal))
            (𝓝[<] H.time i.succ) (𝓝 ((c * (H.horizon - H.time i.succ) : ℝ) : EReal)) :=
          EReal.tendsto_coe.mpr (hreal.tendsto.mono_left nhdsWithin_le_nhds)
        exact le_of_eq hcont.liminf_eq.symm
      dini := by
        intro s hs _
        exact upperRightDiniLE_linearWeight s hs hc hcpi }
    (by linarith)

theorem observedComparisonRecord_nonempty_linear {H : ObservedHistory.{u}} {c : ℝ} (hc : 0 < c)
    (hcpi : 2 * Real.pi ≤ c) (hH : 0 < H.horizon) :
    Nonempty (ObservedComparisonRecord H c (c * H.horizon)) :=
  observedComparisonRecordOfLinearWeight_nonempty hc hcpi hH le_rfl


theorem exists_poincare_controlled_extinction_of_retainedCoreTower_uniformRecordsAbove
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing)
    (hctrl : T.hasPoincareStandardDiscarded)
    {c A : ℝ} (hrec : T.toObservationTower.UniformRecordsAbove c A) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_retainedCoreTower_cutCap M g T hbfr hctrl
    (T.toObservationTower.towerExtinct_of_uniformRecordsAbove hrec)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
