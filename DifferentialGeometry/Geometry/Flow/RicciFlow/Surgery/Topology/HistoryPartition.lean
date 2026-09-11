import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices

noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem stageDomain_subset (j : Fin (H.eventCount + 1)) :
    H.stageDomain j ⊆ Icc 0 H.horizon := by
  cases j using Fin.lastCases with
  | last =>
    intro t ht
    simp only [stageDomain, Fin.lastCases_last, mem_Icc] at ht
    exact ⟨(H.time_nonneg _).trans ht.1, ht.2⟩
  | cast i =>
    intro t ht
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
    exact ⟨(H.time_nonneg _).trans ht.1, ht.2.le.trans (H.time_le_horizon_at _)⟩

theorem mem_stageDomain_iff (t : Icc (0 : ℝ) H.horizon)
    (j : Fin (H.eventCount + 1)) : t.1 ∈ H.stageDomain j ↔ H.activeStage t = j := by
  constructor
  · intro ht
    cases j using Fin.lastCases with
    | last =>
      simp only [stageDomain, Fin.lastCases_last, mem_Icc] at ht
      exact le_antisymm (Fin.le_last _) (H.le_activeStage t _ ht.1)
    | cast i =>
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
      apply H.activeStage_eq_of_maximal t i.castSucc ht.1
      intro k hk
      by_contra hki
      have hnext : i.succ ≤ k := by
        change i.val + 1 ≤ k.val
        have hlt := lt_of_not_ge hki
        change i.val < k.val at hlt
        omega
      exact (not_le_of_gt ht.2) ((H.time_strictMono.monotone hnext).trans hk)
  · intro he
    rw [← he]
    exact H.activeStage_mem t

theorem iUnion_stageDomain : (⋃ j, H.stageDomain j) = Icc 0 H.horizon := by
  apply Subset.antisymm
  · exact iUnion_subset fun j => H.stageDomain_subset j
  · intro t ht
    exact mem_iUnion.mpr ⟨H.activeStage ⟨t, ht⟩, H.activeStage_mem ⟨t, ht⟩⟩

theorem pairwise_disjoint_stageDomain :
    Pairwise (fun i j => Disjoint (H.stageDomain i) (H.stageDomain j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hti htj
  let a : Icc (0 : ℝ) H.horizon := ⟨t, H.stageDomain_subset i hti⟩
  exact hij (((H.mem_stageDomain_iff a i).mp hti).symm.trans
    ((H.mem_stageDomain_iff a j).mp htj))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
