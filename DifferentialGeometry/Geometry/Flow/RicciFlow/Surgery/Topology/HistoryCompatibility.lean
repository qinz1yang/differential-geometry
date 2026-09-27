import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryIdentities

noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem SamePresentation.activeStage {K : ObservedHistory.{u}}
    (R : H.SamePresentation K) (t : Icc (0 : ℝ) H.horizon) :
    Fin.cast (congrArg (· + 1) R.count_eq) (H.activeStage t) =
      K.activeStage ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩ := by
  symm
  apply K.activeStage_eq_of_maximal
  · rw [← R.time_eq]
    exact H.activeStage_time_le t
  · intro k hk
    let j : Fin (H.eventCount + 1) := Fin.cast (congrArg (· + 1) R.count_eq.symm) k
    have hj : Fin.cast (congrArg (· + 1) R.count_eq) j = k := Fin.ext rfl
    have he := R.time_eq j
    rw [hj] at he
    have hle := H.le_activeStage t j (he.trans_le hk)
    exact hle

theorem SamePresentation.restrict {K : ObservedHistory.{u}}
    (R : H.SamePresentation K) (t : Icc (0 : ℝ) H.horizon) :
    (H.restrict t).SamePresentation
      (K.restrict ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩) := by
  let tK : Icc (0 : ℝ) K.horizon :=
    ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩
  let S := H.restrict t
  let T := K.restrict tK
  have hc : S.eventCount = T.eventCount := congrArg Fin.val (SamePresentation.activeStage H R t)
  have htime (j : Fin (S.eventCount + 1)) :
      S.time j = T.time (Fin.cast (congrArg (· + 1) hc) j) := R.time_eq _
  refine {
    horizon_eq := rfl
    count_eq := hc
    time_eq := htime
    stage_eq := fun j => R.stage_eq _
    initialMetric_heq := fun j => R.initialMetric_heq _
    event_eq := fun i => R.event_eq _
    metric_heq := ?_ }
  intro j τ hτ
  have hdom : S.stageDomain j = T.stageDomain (Fin.cast (congrArg (· + 1) hc) j) := by
    cases j using Fin.lastCases with
    | last =>
      have hj : Fin.cast (congrArg (· + 1) hc) (Fin.last S.eventCount) =
          Fin.last T.eventCount := Fin.ext hc
      have he := htime (Fin.last S.eventCount)
      rw [hj] at he ⊢
      dsimp only [S, T] at he ⊢
      simp only [stageDomain, Fin.lastCases_last]
      exact congrArg₂ Icc he rfl
    | cast i =>
      have hj : Fin.cast (congrArg (· + 1) hc) i.castSucc =
          (Fin.cast hc i).castSucc := Fin.ext rfl
      have hs : Fin.cast (congrArg (· + 1) hc) i.succ =
          (Fin.cast hc i).succ := Fin.ext rfl
      have hl := htime i.castSucc
      have hu := htime i.succ
      rw [hj] at hl ⊢
      rw [hs] at hu
      simp only [stageDomain, Fin.lastCases_castSucc]
      exact congrArg₂ Ico hl hu
  have hτK : τ ∈ T.stageDomain (Fin.cast (congrArg (· + 1) hc) j) := by
    rw [← hdom]
    exact hτ
  have hτH := H.restrict_stageDomain_subset t j hτ
  have hm₁ := H.restrict_stageMetric t j τ hτ
  have hm₂ := R.metric_heq _ τ hτH
  have hm₃ := K.restrict_stageMetric tK
    (Fin.cast (congrArg (· + 1) hc) j) τ hτK
  exact (hm₁.trans hm₂).trans hm₃.symm
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification

universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H K : ObservedHistory.{u}}

theorem restrict_heq (A : InitialIdentification P g H)
    (B : InitialIdentification P g K) (hmap : HEq A.map B.map)
    (t : Icc (0 : ℝ) H.horizon) (s : Icc (0 : ℝ) K.horizon) :
    HEq (A.restrict t).map (B.restrict s).map := hmap


theorem restrict_restrict_map (A : InitialIdentification P g H)
    (a : Icc (0 : ℝ) H.horizon) (t : Icc (0 : ℝ) (H.restrict a).horizon) :
    ((A.restrict a).restrict t).map =
      (A.restrict ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩).map := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification
