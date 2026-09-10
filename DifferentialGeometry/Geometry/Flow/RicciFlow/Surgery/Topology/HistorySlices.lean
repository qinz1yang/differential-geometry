import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction

noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})


theorem restrict_activeStage (a : Icc (0 : ℝ) H.horizon)
    (t : Icc (0 : ℝ) (H.restrict a).horizon) :
    Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1)
      ((H.restrict a).activeStage t) =
      H.activeStage ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩ := by
  symm
  apply H.activeStage_eq_of_maximal
  · exact (H.restrict a).activeStage_time_le t
  · intro k hk
    have hka : k ≤ H.activeStage a := H.le_activeStage a k (hk.trans t.2.2)
    let k' : Fin ((H.restrict a).eventCount + 1) :=
      ⟨k.val, by
        change k.val < (H.activeStage a).val + 1
        exact Nat.lt_succ_of_le hka⟩
    have hk' : (H.restrict a).time k' ≤ t.1 := hk
    exact (H.restrict a).le_activeStage t k' hk'

theorem restrict_stageAt (a : Icc (0 : ℝ) H.horizon)
    (t : Icc (0 : ℝ) (H.restrict a).horizon) :
    (H.restrict a).stageAt t = H.stageAt ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩ :=
  congrArg H.stage (H.restrict_activeStage a t)

theorem stageMetric_initial (j : Fin (H.eventCount + 1)) :
    H.stageMetric j (H.time j) = H.initialMetric j := by
  cases j using Fin.lastCases with
  | last =>
    simp only [stageMetric, Fin.lastCases_last]
    split_ifs with h
    · exact H.final_initial h
    · rfl
  | cast i =>
    simpa only [stageMetric, Fin.lastCases_castSucc] using H.event_initial i


theorem restrict_restrict_eventCount (a : Icc (0 : ℝ) H.horizon)
    (t : Icc (0 : ℝ) (H.restrict a).horizon) :
    ((H.restrict a).restrict t).eventCount =
      (H.restrict ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩).eventCount :=
  congrArg Fin.val (H.restrict_activeStage a t)


theorem restrict_horizon_eventCount :
    (H.restrict ⟨H.horizon, H.horizon_nonneg, le_rfl⟩).eventCount = H.eventCount := by
  change (H.activeStage ⟨H.horizon, H.horizon_nonneg, le_rfl⟩).val = H.eventCount
  rw [H.activeStage_at_horizon]
  rfl

theorem restrict_stageMetric (a : Icc (0 : ℝ) H.horizon)
    (j : Fin ((H.restrict a).eventCount + 1))
    (τ : ℝ) (hτ : τ ∈ (H.restrict a).stageDomain j) :
    HEq ((H.restrict a).stageMetric j τ)
      (H.stageMetric
        (Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1) j) τ) := by
  cases j using Fin.lastCases with
  | cast i =>
    change HEq ((H.restrict a).stageMetric i.castSucc τ)
      (H.stageMetric (Fin.castLE (Nat.le_of_lt_succ (H.activeStage a).isLt) i).castSucc τ)
    simp only [stageMetric, Fin.lastCases_castSucc]
    rfl
  | last =>
    simp only [stageDomain, Fin.lastCases_last, Set.mem_Icc] at hτ
    simp only [stageMetric, Fin.lastCases_last]
    change H.time (H.activeStage a) ≤ τ ∧ τ ≤ a.1 at hτ
    change HEq
      ((if h : H.time (H.activeStage a) < a.1 then
        (H.closedPrefixAt a h).flow.base.metric
      else fun _ => H.initialMetric (H.activeStage a)) τ)
      (H.stageMetric (H.activeStage a) τ)
    split_ifs with h
    · exact heq_of_eq (H.closedPrefixAt_metric a h τ)
    · have he : τ = H.time (H.activeStage a) :=
        le_antisymm (hτ.2.trans (not_lt.mp h)) hτ.1
      subst τ
      exact heq_of_eq (H.stageMetric_initial _).symm

theorem activeStage_mem (t : Icc (0 : ℝ) H.horizon) :
    t.1 ∈ H.stageDomain (H.activeStage t) := by
  have hleft := H.activeStage_time_le t
  generalize he : H.activeStage t = k at hleft ⊢
  cases k using Fin.lastCases with
  | last =>
    simpa only [stageDomain, Fin.lastCases_last, Set.mem_Icc] using And.intro hleft t.2.2
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, Set.mem_Ico]
    change H.time i.castSucc ≤ t.1 ∧ t.1 < H.time i.succ
    refine ⟨hleft, ?_⟩
    have hk : (H.activeStage t).val < H.eventCount := by rw [he]; exact i.isLt
    have hn := H.activeStage_before_next t hk
    have hi : (⟨(H.activeStage t).val + 1, by omega⟩ : Fin (H.eventCount + 1)) = i.succ := by
      apply Fin.ext
      change (H.activeStage t).val + 1 = i.val + 1
      have hv := congrArg Fin.val he
      exact congrArg (· + 1) hv
    simpa only [hi] using hn


theorem restrict_sliceMetric (a : Icc (0 : ℝ) H.horizon)
    (t : Icc (0 : ℝ) (H.restrict a).horizon) :
    HEq ((H.restrict a).stageMetric ((H.restrict a).activeStage t) t.1)
      (H.stageMetric (H.activeStage ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩) t.1) := by
  have he := H.restrict_activeStage a t
  have hm := H.restrict_stageMetric a ((H.restrict a).activeStage t) t.1
    ((H.restrict a).activeStage_mem t)
  rw [he] at hm
  exact hm
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
