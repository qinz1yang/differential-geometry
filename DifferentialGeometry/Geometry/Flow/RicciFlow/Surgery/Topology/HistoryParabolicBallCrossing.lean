import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u})

theorem isParabolicallyRmControlledBall.exists_regularCrossing_at_event_time
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r : ℝ}
    (hball : H.isParabolicallyRmControlledBall t p r)
    (i : Fin H.eventCount) (ht : t.val = H.time i.succ) :
    let hi : H.activeStage t = i.succ := H.activeStage_eq_of_maximal t i.succ
      (by rw [ht]) (fun k hk => H.time_strictMono.le_iff_le.mp (by simpa only [ht] using hk))
    ∃ x : (H.event i).incoming.terminalRegularOpen,
      (H.event i).RegularCrossing x.val (hi ▸ p) := by
  intro hi
  obtain ⟨hr, a, hat, ha, htrace⟩ := hball
  have hmem : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨A, _⟩ := htrace p hmem
  have hafirst : H.activeStage a ≤ i.castSucc := by
    have htime : H.time (H.activeStage a) < H.time i.succ :=
      (H.activeStage_time_le a).trans_lt (by rw [ha, ht]; exact sub_lt_self _ (sq_pos_of_pos hr))
    have hlt := H.time_strictMono.lt_iff_lt.mp htime
    exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hlt)
  have hlast (last : Fin (H.eventCount + 1)) (heq : last = i.succ)
      (y : (H.stage last).Carrier) (hle : H.activeStage a ≤ last)
      (B : BackwardPointTrace H (H.activeStage a) last hle y) :
      ∃ x : (H.event i).incoming.terminalRegularOpen,
        (H.event i).RegularCrossing x.val (heq ▸ y) := by
    subst last
    have hcross := B.crossing i hafirst le_rfl
    rw [B.endpoint_eq] at hcross
    exact ⟨⟨_, hcross.mem_terminalRegularRegion (H.event i)⟩, hcross⟩
  exact hlast _ hi p (H.activeStage_mono hat) A

theorem isParabolicallyRmControlledBall.regularCrossing_of_oldOutput_at_event_time
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r : ℝ}
    (hball : H.isParabolicallyRmControlledBall t p r)
    (i : Fin H.eventCount) (ht : t.val = H.time i.succ) :
    let hi : H.activeStage t = i.succ := H.activeStage_eq_of_maximal t i.succ
      (by rw [ht]) (fun k hk => H.time_strictMono.le_iff_le.mp (by simpa only [ht] using hk))
    ∀ z : (H.event i).old, (H.event i).oldOutput z = (hi ▸ p) →
      (H.event i).RegularCrossing z.val.val (hi ▸ p) := by
  intro hi z hz
  obtain ⟨x, hx⟩ := hball.exists_regularCrossing_at_event_time H i ht
  rw [(H.event i).oldOutput_eq_iff_of_regularCrossing z hx |>.mp hz]
  exact hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
