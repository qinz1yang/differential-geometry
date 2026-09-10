import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation

noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})
private theorem stageDomain_of_le (j : Fin (H.eventCount + 1))
    {a τ : ℝ} (ha : a ∈ H.stageDomain j) (hleft : H.time j ≤ τ) (hright : τ ≤ a) :
    τ ∈ H.stageDomain j := by
  cases j using Fin.lastCases with
  | last =>
    simp only [stageDomain, Fin.lastCases_last, Set.mem_Icc] at ha ⊢
    exact ⟨hleft, hright.trans ha.2⟩
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at ha ⊢
    exact ⟨hleft, hright.trans_lt ha.2⟩


theorem restrict_stageDomain_subset (a : Icc (0 : ℝ) H.horizon)
    (j : Fin ((H.restrict a).eventCount + 1)) :
    (H.restrict a).stageDomain j ⊆
      H.stageDomain
        (Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1) j) := by
  cases j using Fin.lastCases with
  | cast i =>
    change (H.restrict a).stageDomain i.castSucc ⊆
      H.stageDomain (Fin.castLE (Nat.le_of_lt_succ (H.activeStage a).isLt) i).castSucc
    simp only [stageDomain, Fin.lastCases_castSucc]
    exact Subset.rfl
  | last =>
    intro τ hτ
    simp only [stageDomain, Fin.lastCases_last, Set.mem_Icc] at hτ
    exact H.stageDomain_of_le (H.activeStage a) (H.activeStage_mem a) hτ.1 hτ.2
private theorem stageDomain_eq_of_data (K : ObservedHistory.{u})
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

theorem restrict_restrict (a : Icc (0 : ℝ) H.horizon)
    (t : Icc (0 : ℝ) (H.restrict a).horizon) :
    ((H.restrict a).restrict t).SamePresentation
      (H.restrict ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩) := by
  let S := H.restrict a
  let T := S.restrict t
  let U := H.restrict ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩
  have hc : T.eventCount = U.eventCount := H.restrict_restrict_eventCount a t
  have htime (j : Fin (T.eventCount + 1)) :
      T.time j = U.time (Fin.cast (congrArg (· + 1) hc) j) := rfl
  refine {
    horizon_eq := rfl
    count_eq := hc
    time_eq := htime
    stage_eq := fun _ => rfl
    initialMetric_heq := fun _ => HEq.rfl
    event_eq := fun i => MetricCutCapEvent.SamePresentation.refl _
    metric_heq := ?_ }
  intro j τ hτ
  have hdom := T.stageDomain_eq_of_data U hc rfl htime j
  have hu : τ ∈ U.stageDomain (Fin.cast (congrArg (· + 1) hc) j) := by
    rw [← hdom]
    exact hτ
  have hs := S.restrict_stageDomain_subset t j hτ
  have hm₁ := S.restrict_stageMetric t j τ hτ
  have hm₂ := H.restrict_stageMetric a _ τ hs
  have hm₃ := H.restrict_stageMetric
    ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩ (Fin.cast (congrArg (· + 1) hc) j) τ hu
  exact (hm₁.trans hm₂).trans hm₃.symm

theorem restrict_self :
    (H.restrict ⟨H.horizon, H.horizon_nonneg, le_rfl⟩).SamePresentation H := by
  have hc := H.restrict_horizon_eventCount
  refine {
    horizon_eq := rfl
    count_eq := hc
    time_eq := fun _ => rfl
    stage_eq := fun _ => rfl
    initialMetric_heq := fun _ => HEq.rfl
    event_eq := fun i => MetricCutCapEvent.SamePresentation.refl _
    metric_heq := ?_ }
  intro j τ hτ
  exact H.restrict_stageMetric ⟨H.horizon, H.horizon_nonneg, le_rfl⟩ j τ hτ
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
