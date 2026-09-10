import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRescaling

noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

private theorem stageMetric_last (H : ObservedHistory.{u}) (t : ℝ) :
    H.stageMetric (Fin.last H.eventCount) t =
      (if h : H.time (Fin.last H.eventCount) < H.horizon then
        (H.finalSlab h).flow.base.metric
      else fun _ => H.initialMetric (Fin.last H.eventCount)) t := by
  simp only [stageMetric, Fin.lastCases_last]

private theorem stageMetric_castSucc (H : ObservedHistory.{u})
    (i : Fin H.eventCount) (t : ℝ) :
    H.stageMetric i.castSucc t = (H.event i).incoming.flow.base.metric t := by
  simp only [stageMetric, Fin.lastCases_castSucc]

theorem rescale_activeStage (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r)
    (t : Icc (0 : ℝ) H.horizon) :
    (H.rescale r hr).activeStage
      ⟨t.1 / r, div_nonneg t.2.1 hr.le, (div_le_div_iff_of_pos_right hr).mpr t.2.2⟩ =
      H.activeStage t := by
  apply (H.rescale r hr).activeStage_eq_of_maximal
  · exact (div_le_div_iff_of_pos_right hr).mpr (H.activeStage_time_le t)
  · intro j hj
    exact H.le_activeStage t j ((div_le_div_iff_of_pos_right hr).mp hj)

theorem rescale_stageMetric (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r)
    (j : Fin (H.eventCount + 1)) (t : ℝ) :
    (H.rescale r hr).stageMetric j t =
      scaleMetric r⁻¹ (inv_pos.mpr hr) (H.stageMetric j (r * t)) := by
  cases j using Fin.lastCases with
  | last =>
    change (H.rescale r hr).stageMetric (Fin.last (H.rescale r hr).eventCount) t =
      scaleMetric r⁻¹ (inv_pos.mpr hr) (H.stageMetric (Fin.last H.eventCount) (r * t))
    rw [stageMetric_last (H.rescale r hr) t, stageMetric_last H (r * t)]
    by_cases h : H.time (Fin.last H.eventCount) < H.horizon
    · have hs : (H.rescale r hr).time (Fin.last (H.rescale r hr).eventCount) <
          (H.rescale r hr).horizon :=
        (div_lt_div_iff_of_pos_right hr).mpr h
      rw [dif_pos hs, dif_pos h]
      change ((H.finalSlab h).rescale r hr).flow.base.metric t =
        scaleMetric r⁻¹ (inv_pos.mpr hr) ((H.finalSlab h).flow.base.metric (r * t))
      exact OrientedThreeStage.ClosedSlab.rescale_metric (H.finalSlab h) r hr t
    · have hs : ¬(H.rescale r hr).time (Fin.last (H.rescale r hr).eventCount) <
          (H.rescale r hr).horizon :=
        fun hh => h ((div_lt_div_iff_of_pos_right hr).mp hh)
      rw [dif_neg hs, dif_neg h]
      rfl
  | cast i =>
    let i' : Fin (H.rescale r hr).eventCount := i
    change (H.rescale r hr).stageMetric i'.castSucc t =
      scaleMetric r⁻¹ (inv_pos.mpr hr) (H.stageMetric i.castSucc (r * t))
    rw [stageMetric_castSucc (H.rescale r hr) i' t, stageMetric_castSucc H i (r * t)]
    exact MetricCutCapEvent.rescale_incoming_metric (H.event i) r hr t

theorem rescale_stageDomain (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r)
    (j : Fin (H.eventCount + 1)) :
    (H.rescale r hr).stageDomain j = (fun t => r * t) ⁻¹' H.stageDomain j := by
  cases j using Fin.lastCases with
  | last =>
    ext t
    simp only [stageDomain, rescale, Fin.lastCases_last,
      mem_Icc, mem_preimage, div_le_iff₀ hr, le_div_iff₀ hr, mul_comm t r]
  | cast i =>
    ext t
    simp only [stageDomain, rescale, Fin.lastCases_castSucc,
      mem_Ico, mem_preimage, div_le_iff₀ hr, lt_div_iff₀ hr, mul_comm t r]

private theorem stageDomain_eq_of_count_time {H K : ObservedHistory.{u}}
    (hc : H.eventCount = K.eventCount) (hh : H.horizon = K.horizon)
    (ht : ∀ j : Fin (H.eventCount + 1),
      H.time j = K.time (Fin.cast (congrArg (· + 1) hc) j))
    (j : Fin (H.eventCount + 1)) :
    H.stageDomain j = K.stageDomain (Fin.cast (congrArg (· + 1) hc) j) := by
  cases j using Fin.lastCases with
  | last =>
    have hj : Fin.cast (congrArg (· + 1) hc) (Fin.last H.eventCount) =
        Fin.last K.eventCount := Fin.ext hc
    have he := ht (Fin.last H.eventCount)
    rw [hj] at he ⊢
    simp only [stageDomain, Fin.lastCases_last]
    exact congrArg₂ Icc he hh
  | cast i =>
    have hj : Fin.cast (congrArg (· + 1) hc) i.castSucc =
        (Fin.cast hc i).castSucc := Fin.ext rfl
    have hs : Fin.cast (congrArg (· + 1) hc) i.succ =
        (Fin.cast hc i).succ := Fin.ext rfl
    have hl := ht i.castSucc
    have hu := ht i.succ
    rw [hj] at hl ⊢
    rw [hs] at hu
    simp only [stageDomain, Fin.lastCases_castSucc]
    exact congrArg₂ Ico hl hu

theorem restrict_rescale (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (r : ℝ) (hr : 0 < r) :
    ((H.restrict t).rescale r hr).SamePresentation
      ((H.rescale r hr).restrict
        ⟨t.1 / r, div_nonneg t.2.1 hr.le, (div_le_div_iff_of_pos_right hr).mpr t.2.2⟩) := by
  let s : Icc (0 : ℝ) (H.rescale r hr).horizon :=
    ⟨t.1 / r, div_nonneg t.2.1 hr.le, (div_le_div_iff_of_pos_right hr).mpr t.2.2⟩
  let S := (H.restrict t).rescale r hr
  let T := (H.rescale r hr).restrict s
  have hc : S.eventCount = T.eventCount :=
    (congrArg Fin.val (H.rescale_activeStage r hr t)).symm
  have htime (j : Fin (S.eventCount + 1)) :
      S.time j = T.time (Fin.cast (congrArg (· + 1) hc) j) := rfl
  refine {
    horizon_eq := rfl
    count_eq := hc
    time_eq := htime
    stage_eq := fun _ => rfl
    initialMetric_heq := fun _ => HEq.rfl
    event_eq := fun _ => MetricCutCapEvent.SamePresentation.refl _
    metric_heq := ?_ }
  intro j τ hτ
  have hdom := stageDomain_eq_of_count_time hc rfl htime j
  have hτT : τ ∈ T.stageDomain (Fin.cast (congrArg (· + 1) hc) j) := by
    rw [← hdom]
    exact hτ
  have hτOld : r * τ ∈ (H.restrict t).stageDomain j := by
    change τ ∈ ((H.restrict t).rescale r hr).stageDomain j at hτ
    exact (congrArg (fun U : Set ℝ => τ ∈ U)
      ((H.restrict t).rescale_stageDomain r hr j)).mp hτ
  have hmOld := H.restrict_stageMetric t j (r * τ) hτOld
  have hmNew := (H.rescale r hr).restrict_stageMetric s
    (Fin.cast (congrArg (· + 1) hc) j) τ hτT
  have hnew := hmNew.trans (heq_of_eq (H.rescale_stageMetric r hr _ τ))
  exact (heq_of_eq ((H.restrict t).rescale_stageMetric r hr j τ)).trans
    ((heq_of_eq (congrArg (fun g => scaleMetric r⁻¹ (inv_pos.mpr hr) g)
      (eq_of_heq hmOld))).trans hnew.symm)

end ObservedHistory

namespace InitialIdentification

theorem restrict_rescale_map {P : OrientedThreeStage.{u}} {g : P.Metric}
    {H : ObservedHistory.{u}} (A : InitialIdentification P g H)
    (t : Icc (0 : ℝ) H.horizon) (r : ℝ) (hr : 0 < r) :
    HEq ((A.restrict t).rescale r hr).map
      ((A.rescale r hr).restrict
        ⟨t.1 / r, div_nonneg t.2.1 hr.le, (div_le_div_iff_of_pos_right hr).mpr t.2.2⟩).map :=
  HEq.rfl

end InitialIdentification

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
