import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ScalarNonnegativeSmooth_CX9
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeScalar_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeAssembly_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition

set_option autoImplicit false

/-!
# CH12-CX9: propagation from an arbitrary nonnegative slice

The finite-history induction starts at the active stage of the chosen time.
Earlier stages are unrestricted. The tower comparison uses actual stage equality
and metric `HEq`, so it also identifies total volumes on different carriers.
-/

noncomputable section

open Set Filter MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

/-- Smooth propagation within one history stage, from any time in its domain. -/
theorem stage_nonnegative_volume_CX9 (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) {a b : ℝ}
    (ha : a ∈ H.stageDomain j) (hb : b ∈ H.stageDomain j) (hab : a ≤ b)
    (hinit : ∀ x, 0 ≤ metricScalarAt (H.stageMetric j a) x) :
    (∀ x, 0 ≤ metricScalarAt (H.stageMetric j b) x) ∧
      riemannianVolumeMeasure ThreeModel (H.stage j).Carrier (H.stageMetric j b) univ ≤
        riemannianVolumeMeasure ThreeModel (H.stage j).Carrier (H.stageMetric j a) univ := by
  have ha0 : 0 ≤ a := (H.stageDomain_subset j ha).1
  cases j using Fin.lastCases with
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at ha hb
    simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc] at hinit ⊢
    exact smooth_nonnegative_volume_CX9 ha0 hab (H.event i).incoming.flow
      (H.event i).incoming.equation
      (fun t ht => ⟨ha.1.trans ht.1, ht.2.trans_lt hb.2⟩)
      (fun t ht => ⟨ha.1.trans_lt ht.1, ht.2.trans hb.2⟩) hinit
  | last =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc] at ha hb
    simp only [ObservedHistory.stageMetric, Fin.lastCases_last] at hinit ⊢
    split_ifs at hinit ⊢ with h
    · exact smooth_nonnegative_volume_CX9 ha0 hab (H.finalSlab h).flow
        (H.finalSlab h).equation
        (fun t ht => ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩)
        (fun t ht => ⟨ha.1.trans_lt ht.1, ht.2.trans_le hb.2⟩) hinit
    · exact ⟨hinit, le_rfl⟩

/-- A stage's initial time belongs to its domain. -/
theorem stage_start_mem_CX9 (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) :
    H.time j ∈ H.stageDomain j := by
  have h := H.activeStage_mem (H.stageTime j)
  rwa [H.activeStage_stageTime] at h

/-- The left endpoint is a lower bound for every time in a stage domain. -/
theorem stage_start_le_CX9 (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1))
    {t : ℝ} (ht : t ∈ H.stageDomain j) : H.time j ≤ t := by
  cases j using Fin.lastCases with
  | last =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc] at ht
    exact ht.1
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
    exact ht.1

/-- Finite-history propagation, with no hypothesis before the starting time. -/
theorem history_nonnegative_volume_CX9 (H : ObservedHistory.{u})
    {parameters : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (a : Icc (0 : ℝ) H.horizon) (V : ℝ≥0∞)
    (hinit : ∀ x, 0 ≤ metricScalarAt (H.stageMetric (H.activeStage a) a) x)
    (hV : riemannianVolumeMeasure ThreeModel (H.stage (H.activeStage a)).Carrier
      (H.stageMetric (H.activeStage a) a) univ ≤ V) :
    ∀ j : Fin (H.eventCount + 1), H.activeStage a ≤ j →
      ∀ t ∈ H.stageDomain j, a.val ≤ t →
        (∀ x, 0 ≤ metricScalarAt (H.stageMetric j t) x) ∧
          riemannianVolumeMeasure ThreeModel (H.stage j).Carrier
            (H.stageMetric j t) univ ≤ V := by
  have hbase (j : Fin (H.eventCount + 1)) (hj : j = H.activeStage a)
      (t : ℝ) (ht : t ∈ H.stageDomain j) (hat : a.val ≤ t) :
      (∀ x, 0 ≤ metricScalarAt (H.stageMetric j t) x) ∧
        riemannianVolumeMeasure ThreeModel (H.stage j).Carrier
          (H.stageMetric j t) univ ≤ V := by
    subst j
    obtain ⟨hs, hv⟩ := stage_nonnegative_volume_CX9 H (H.activeStage a)
      (H.activeStage_mem a) ht hat hinit
    exact ⟨hs, hv.trans hV⟩
  refine Fin.induction (motive := fun j => H.activeStage a ≤ j →
    ∀ t ∈ H.stageDomain j, a.val ≤ t →
      (∀ x, 0 ≤ metricScalarAt (H.stageMetric j t) x) ∧
        riemannianVolumeMeasure ThreeModel (H.stage j).Carrier
          (H.stageMetric j t) univ ≤ V) ?_ ?_
  · intro hj t ht hat
    exact hbase 0 (le_antisymm (Fin.zero_le _) hj) t ht hat
  · intro i ih hj t ht hat
    by_cases heq : i.succ = H.activeStage a
    · exact hbase i.succ heq t ht hat
    have hprev : H.activeStage a ≤ i.castSucc := by
      have hlt : H.activeStage a < i.succ := lt_of_le_of_ne hj (Ne.symm heq)
      change (H.activeStage a).val ≤ i.val
      change (H.activeStage a).val < i.val + 1 at hlt
      omega
    have hanext : a.val < H.time i.succ := by
      by_contra hnot
      have hle := H.le_activeStage a i.succ (not_lt.mp hnot)
      exact (not_le_of_gt (Fin.castSucc_lt_succ (i := i))) (hle.trans hprev)
    have htime : H.time i.castSucc < H.time i.succ :=
      H.time_strictMono (Fin.castSucc_lt_succ (i := i))
    have htail : ∀ᶠ v in 𝓝[<] H.time i.succ,
        (∀ x, 0 ≤ metricScalarAt ((H.event i).incoming.flow.base.metric v) x) ∧
          riemannianVolumeMeasure ThreeModel (H.stage i.castSucc).Carrier
            ((H.event i).incoming.flow.base.metric v) univ ≤ V := by
      filter_upwards [Ioo_mem_nhdsLT (max_lt hanext htime)] with v hv
      have hvdom : v ∈ H.stageDomain i.castSucc := by
        simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico]
        exact ⟨(le_max_right _ _).trans hv.1.le, hv.2⟩
      have h := ih hprev v hvdom ((le_max_left _ _).trans hv.1.le)
      simpa only [ObservedHistory.stageMetric, Fin.lastCases_castSucc] using h
    have hnext := event_nonnegative_of_eventually_CX9 (records i) (htail.mono fun _ h => h.1)
    have hvnext := event_volume_le_of_eventually_CX9 (records i) V (htail.mono fun _ h => h.2)
    rw [← H.stageMetric_initial i.succ] at hnext hvnext
    obtain ⟨hs, hv⟩ := stage_nonnegative_volume_CX9 H i.succ (stage_start_mem_CX9 H _)
      ht (stage_start_le_CX9 H _ ht) hnext
    exact ⟨hs, hv.trans hvnext⟩

/-- Transport scalar and total-volume assertions along actual stage/metric identifications. -/
theorem nonnegative_volume_transport_CX9 {A B : OrientedThreeStage.{u}}
    (hAB : A = B) {gA : A.Metric} {gB : B.Metric} (hg : HEq gA gB) {V : ℝ≥0∞}
    (h : (∀ x, 0 ≤ metricScalarAt gA x) ∧
      riemannianVolumeMeasure ThreeModel A.Carrier gA univ ≤ V) :
    (∀ x, 0 ≤ metricScalarAt gB x) ∧
      riemannianVolumeMeasure ThreeModel B.Carrier gB univ ≤ V := by
  subst hAB
  cases eq_of_heq hg
  exact h

/-- A regular slice agrees with the corresponding slice in any sufficiently long tower history. -/
theorem regularSlice_tower_identification_CX9 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {O : ObservationTower P g} (s : RegularSlice O) (n : ℕ) (hn : s.time ≤ (n : ℝ)) :
    let H := O.history n
    let t : Icc (0 : ℝ) H.horizon := ⟨s.time, s.positive.le, by rw [O.horizon_eq]; exact hn⟩
    s.stage = H.stage (H.activeStage t) ∧ HEq s.metric (H.stageMetric (H.activeStage t) t) := by
  intro H t
  let R := O.observe_eq_atIndex n s.time s.positive.le hn
  let J := O.atIndex n s.time s.positive.le hn
  have hlast : Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last s.history.eventCount) =
      Fin.last J.eventCount := Fin.ext R.count_eq
  have hs := R.stage_eq (Fin.last s.history.eventCount)
  have hm := R.metric_heq (Fin.last s.history.eventCount) s.time (by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc]
    exact ⟨s.preceding.le, le_rfl⟩)
  rw [hlast] at hs hm
  have hj : Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage t).isLt) 1)
      (Fin.last (H.restrict t).eventCount) = H.activeStage t := Fin.ext rfl
  have hr := H.restrict_stageMetric t (Fin.last (H.restrict t).eventCount) s.time (by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc]
    exact ⟨H.activeStage_time_le t, le_rfl⟩)
  rw [hj] at hr
  exact ⟨hs, hm.trans hr⟩

/-- Nonnegative scalar curvature persists and physical total volume cannot increase. -/
theorem regularSlice_nonnegative_volume_CX9 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (s₀ s : RegularSlice F.observation) (ht : s₀.time ≤ s.time)
    (h₀ : ∀ x, 0 ≤ metricScalarAt s₀.metric x) :
    (∀ x, 0 ≤ metricScalarAt s.metric x) ∧ sliceTotalVolume_S10 s ≤ sliceTotalVolume_S10 s₀ := by
  let n := Nat.ceil s.time
  let H := F.observation.history n
  have hsN : s.time ≤ (n : ℝ) := Nat.le_ceil _
  have h₀N : s₀.time ≤ (n : ℝ) := ht.trans hsN
  let a : Icc (0 : ℝ) H.horizon :=
    ⟨s₀.time, s₀.positive.le, by rw [F.observation.horizon_eq]; exact h₀N⟩
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨s.time, s.positive.le, by rw [F.observation.horizon_eq]; exact hsN⟩
  obtain ⟨he₀, hm₀⟩ := regularSlice_tower_identification_CX9 s₀ n h₀N
  obtain ⟨he, hm⟩ := regularSlice_tower_identification_CX9 s n hsN
  have hstart := nonnegative_volume_transport_CX9 he₀ hm₀ (V := sliceTotalVolume_S10 s₀)
    ⟨h₀, le_rfl⟩
  have hend := history_nonnegative_volume_CX9 H (Hp.records n) a
    (sliceTotalVolume_S10 s₀) hstart.1 hstart.2 (H.activeStage b)
    (H.activeStage_mono ht) s.time (H.activeStage_mem b) ht
  exact nonnegative_volume_transport_CX9 he.symm hm.symm hend

end GC.LongTime.Ch12
