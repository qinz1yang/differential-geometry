import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingTerminal
noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

open private slabMetric_restrict_eq_localPull from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction

open private incomingMetric_restrict_eq_localPull from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction

theorem exists_incoming_prefix (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (s : Icc (0 : ℝ) H.horizon) (hfirst : H.time first < s.val) :
    ∃ (last : Fin (H.eventCount + 1)) (hfl : first ≤ last)
      (hla : last ≤ H.activeStage s)
      (G : (H.stage last).IncomingSlab (H.time last) s.val),
      Nonempty G.TerminalLimitMetric ∧
      s.val ≤ H.stageEndTime last ∧
      (∀ t : ℝ, G.flow.base.metric t = H.stageMetric last t) ∧
      ∀ (x : (H.stage (H.activeStage s)).Carrier)
        (A : BackwardPointTrace H first (H.activeStage s) (hfl.trans hla) x),
        A.point last hfl hla ∈ G.terminalRegularRegion := by
  by_cases hstrict : H.time (H.activeStage s) < s.val
  · let C := H.closedPrefixAt s hstrict
    refine ⟨H.activeStage s, H.le_activeStage s first hfirst.le, le_rfl,
      C.restrictIncoming le_rfl C.lt le_rfl, ⟨C.endpointTerminalLimitMetric _⟩,
      H.le_stageEndTime_of_mem_stageDomain (H.activeStage_mem s), ?_, ?_⟩
    · intro t
      exact H.closedPrefixAt_metric s hstrict t
    · intro x A
      rw [C.terminalRegularRegion_eq_univ]
      trivial
  · have heq : H.time (H.activeStage s) = s.val :=
      le_antisymm (H.activeStage_time_le s) (le_of_not_gt hstrict)
    have hnzero : H.activeStage s ≠ 0 := by
      intro hz
      rw [hz, H.time_zero] at heq
      have := H.time_nonneg first
      linarith
    obtain ⟨i, hi⟩ := (Fin.eq_zero_or_eq_succ (H.activeStage s)).resolve_left hnzero
    have hsi : s.val = H.time i.succ := by rw [← hi, heq]
    have hfi : first ≤ i.castSucc := by
      have hlt : first < i.succ := H.time_strictMono.lt_iff_lt.mp (hfirst.trans_eq hsi)
      change first.val ≤ i.val
      exact Nat.le_of_lt_succ hlt
    have hia : i.castSucc ≤ H.activeStage s := by rw [hi]; exact i.castSucc_lt_succ.le
    rcases s with ⟨s, hs⟩
    change s = H.time i.succ at hsi
    subst s
    refine ⟨i.castSucc, hfi, hia, (H.event i).incoming, ⟨(H.event i).terminal⟩, ?_, ?_, ?_⟩
    · exact le_of_eq (H.stageEndTime_castSucc i).symm
    · intro t
      simp only [stageMetric, Fin.lastCases_castSucc]
    · intro x A
      have hcross := A.crossing i hfi (show i.succ ≤ H.activeStage ⟨H.time i.succ, hs⟩ by rw [hi])
      exact hcross.mem_terminalRegularRegion (H.event i)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
