import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostSurgeryMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialScalarBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set

namespace GC.LongTime

universe u

private theorem stageMetric_scalarLowerBarrier_of_cutoff_records
    (H : ObservedHistory.{u}) {parameters : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {c : ℝ} (hc : 0 < c)
    (hzero : ∀ x : (H.stage 0).Carrier,
      -3 / (2 * (H.time 0 + c)) ≤ metricScalarAt (H.initialMetric 0) x)
    (j : Fin (H.eventCount + 1)) {t : ℝ} (ht : t ∈ H.stageDomain j)
    (x : (H.stage j).Carrier) :
    -3 / (2 * (t + c)) ≤ metricScalarAt (H.stageMetric j t) x := by
  have hstage := stageInitial_scalarLowerBound_of_history records hc hzero
  cases j using Fin.lastCases with
  | last =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last] at ht
    by_cases hfin : H.time (Fin.last H.eventCount) < H.horizon
    · have hmetric : H.stageMetric (Fin.last H.eventCount) t =
          (H.finalSlab hfin).flow.base.metric t := by
        simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hfin]
      rw [hmetric]
      exact closedSlab_scalarLowerBarrier_le hfin (H.time_nonneg _) hc (H.finalSlab hfin)
        (fun z => by rw [H.final_initial hfin]; exact hstage _ z) ht x
    · have ht' : t = H.time (Fin.last H.eventCount) :=
        le_antisymm (ht.2.trans (le_of_not_gt hfin)) ht.1
      have hmetric : H.stageMetric (Fin.last H.eventCount) t =
          H.initialMetric (Fin.last H.eventCount) := by
        simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_right hfin]
      rw [hmetric, ht']
      exact hstage _ x
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at ht
    have hmetric : H.stageMetric i.castSucc t = (H.event i).incoming.flow.base.metric t := by
      simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    rw [hmetric]
    exact incomingSlab_scalarLowerBarrier_le (H.time_nonneg _) hc (H.event i).incoming
      (fun z => by rw [H.event_initial i]; exact hstage _ z) ht x

theorem exists_postMetric_curvature_bounds_of_cutoff_records
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (parameters : ℕ → CutoffParameters)
    (records : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i (parameters n)) :
    ∃ a : ℝ, 0 < a ∧ ∀ t, 0 ≤ t → ∀ x : (postStage F.observation t).Carrier,
      InFixedHamiltonIveyRegion (postMetric F.observation t) (a + t) x ∧
        -3 / (2 * (t + a / 2)) ≤ metricScalarAt (postMetric F.observation t) x := by
  obtain ⟨a, ha, hfixed, hscalar⟩ :=
    exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  refine ⟨a, ha, ?_⟩
  intro t ht x
  let n := Nat.ceil (max t 0)
  let H := (F.tower.history n).toHistory
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨max t 0, le_max_right t 0, by
      change max t 0 ≤ (F.tower.history n).horizon
      rw [F.tower.horizon_eq]
      exact Nat.le_ceil (max t 0)⟩
  have hzero := (F.tower.initial n).fixedHamiltonIveyRegion_and_scalar_lower_bound
    hfixed hscalar
  have hpinching := H.fixedHamiltonIveyRegion_and_scalar_lower
    (records n) ha hzero.1 hzero.2
  have hscalarZero : ∀ y : (H.stage 0).Carrier,
      -3 / (2 * (H.time 0 + a / 2)) ≤ metricScalarAt (H.initialMetric 0) y := by
    intro y
    simpa only [H.time_zero, zero_add, show 2 * (a / 2) = a by ring] using hzero.2 y
  have hdomain : max t 0 ∈ (H.restrict b).stageDomain
      (Fin.last (H.restrict b).eventCount) := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc]
    exact ⟨H.activeStage_time_le b, le_rfl⟩
  have hmetric : postMetric F.observation t =
      H.stageMetric (H.activeStage b) (max t 0) :=
    eq_of_heq (H.restrict_stageMetric b (Fin.last (H.restrict b).eventCount)
      (max t 0) hdomain)
  have hpin := (hpinching.1 (H.activeStage b) (max t 0) (H.activeStage_mem b) x).1
  have hsc := stageMetric_scalarLowerBarrier_of_cutoff_records H (records n)
    (half_pos ha) hscalarZero (H.activeStage b) (t := max t 0) (H.activeStage_mem b) x
  rw [hmetric]
  constructor
  · have hparameter : a + t = a + max t 0 := by rw [max_eq_left ht]
    rw [hparameter]
    exact hpin
  · have hparameter : -3 / (2 * (t + a / 2)) =
        -3 / (2 * (max t 0 + a / 2)) := by rw [max_eq_left ht]
    rw [hparameter]
    exact hsc

end GC.LongTime
