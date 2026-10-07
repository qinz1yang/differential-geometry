import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventRightFamily_S38
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.TowerFinitePrefixes

set_option autoImplicit false

/-!
# CH12-O75 G2a: right smooth family at any positive time, right regular slices

`exists_right_family_O75`: the S38 GLUE (`exists_smooth_right_family_S38`) without the event-time
hypothesis: just after any `t > 0` the post stage is one fixed stage `Q` carrying one smooth family
`G`, and `postMetric s ≅ G s`.  `hRegRight_O75`: regular slices arbitrarily close to the right of
`t` with the same post stage (the `hRegRight` binder of `[FROZEN] CH12-O66 hEvt_of_parts`).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

section Observe
variable {P : OrientedThreeStage.{u}} {g : P.Metric} (O : ObservationTower P g)

/-- No event in `(t, t + ε0]` forces the last stage of `observe b` (`b ∈ [t, t + ε0]`) to start
by time `t`. -/
theorem observe_last_time_le_O75 {t ε0 b : ℝ} (ht : 0 < t)
    (hgap : ∀ s ∈ O.eventTimes, t < s → s ≤ t + ε0 → False) (htb : t ≤ b) (hb : b ≤ t + ε0) :
    (O.observe b (ht.le.trans htb)).time
      (Fin.last (O.observe b (ht.le.trans htb)).eventCount) ≤ t := by
  set HB := O.observe b (ht.le.trans htb) with hHB
  have hEv : HB.eventTimes = O.eventTimes ∩ Ioc 0 b :=
    (O.eventTimes_inter _ (ht.le.trans htb)).symm
  rcases Fin.eq_zero_or_eq_succ (Fin.last HB.eventCount) with h0 | ⟨j, hj⟩
  · rw [h0, HB.time_zero]; exact ht.le
  · have hmem : HB.time (Fin.last HB.eventCount) ∈ HB.eventTimes := ⟨j, hj ▸ rfl⟩
    rw [hEv] at hmem
    by_contra hcon
    exact hgap _ hmem.1 (not_le.mp hcon) (hmem.2.2.trans hb)

/-- The data behind both results: an event-free gap `(t, t + ε0]`, a fixed stage `Q`, a smooth
family `G` on `[t, t + ε0]` with `postStage s = Q`, `postMetric s ≅ G s` there. -/
theorem rightData_O75 (t : ℝ) (ht : 0 < t) :
    ∃ (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric) (ε0 : ℝ), 0 < ε0 ∧
      (∀ s ∈ O.eventTimes, t < s → s ≤ t + ε0 → False) ∧
      Q.MetricSmoothUpTo G (Icc t (t + ε0)) ∧
      ∀ s : ℝ, t ≤ s → s ≤ t + ε0 → ∃ _ : postStage O s = Q, HEq (postMetric O s) (G s) := by
  obtain ⟨ε0, hε0, -, hgap⟩ := exists_eventFree_gap_S38 O (te := t)
  have htb : t ≤ t + ε0 := by linarith
  have hb : 0 ≤ t + ε0 := by linarith
  set HB := O.observe (t + ε0) hb with hHB
  have htl : HB.time (Fin.last HB.eventCount) ≤ t :=
    observe_last_time_le_O75 O ht hgap htb le_rfl
  have hlt : HB.time (Fin.last HB.eventCount) < t + ε0 := by linarith
  have hlt2 : HB.time (Fin.last HB.eventCount) < HB.horizon := hlt
  have hfs : ∀ τ, HB.stageMetric (Fin.last HB.eventCount) τ =
      (HB.finalSlab hlt).flow.base.metric τ := by
    intro τ
    simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hlt2]
  have hsmooth : (HB.stage (Fin.last HB.eventCount)).MetricSmoothUpTo
      (HB.stageMetric (Fin.last HB.eventCount)) (Icc t (t + ε0)) := by
    have hG : HB.stageMetric (Fin.last HB.eventCount) = (HB.finalSlab hlt).flow.base.metric :=
      funext hfs
    rw [hG]
    refine (HB.finalSlab hlt).smoothUpTo.mono ?_
    intro x hx
    exact ⟨htl.trans hx.1, hx.2⟩
  have hk : ∀ a (ha : 0 ≤ a) (hab : a ≤ t + ε0), t ≤ a →
      HB.activeStage ⟨a, ha, hab⟩ = Fin.last HB.eventCount := fun a ha hab hta =>
    le_antisymm (Fin.le_last _) (HB.le_activeStage _ _ (htl.trans hta))
  refine ⟨HB.stage (Fin.last HB.eventCount), HB.stageMetric (Fin.last HB.eventCount), ε0, hε0,
    hgap, hsmooth, fun s hts hs2 => ?_⟩
  have hs0 : 0 ≤ s := ht.le.trans hts
  obtain ⟨e, hm⟩ := observe_last_eq_S38 O s (t + ε0) hs0 hb hs2 (hk s hs0 hs2 hts) hlt
  exact ⟨(postStage_eq_observe_S38 O s hs0).1.trans e,
    (postStage_eq_observe_S38 O s hs0).2.trans (hm s (htl.trans hts) le_rfl)⟩

/-- `[FROZEN] CH12-O75 G2`: the right smooth family at any `t > 0`. -/
theorem exists_right_family_O75 (t : ℝ) (ht : 0 < t) :
    ∃ (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric) (ε0 : ℝ), 0 < ε0 ∧
      Q.MetricSmoothUpTo G (Icc t (t + ε0)) ∧
      ∀ s : ℝ, t ≤ s → s ≤ t + ε0 → ∃ _ : postStage O s = Q, HEq (postMetric O s) (G s) := by
  obtain ⟨Q, G, ε0, hε0, -, hG, hs⟩ := rightData_O75 O t ht
  exact ⟨Q, G, ε0, hε0, hG, hs⟩

/-- `[FROZEN] CH12-O75 G2` = the `hRegRight` binder of `[FROZEN] CH12-O66 hEvt_of_parts`. -/
theorem hRegRight_O75 :
    ∀ t : ℝ, 0 < t → ∀ δ : ℝ, 0 < δ → ∃ s : RegularSlice O,
      t ≤ s.time ∧ s.time < t + δ ∧ postStage O t = postStage O s.time := by
  intro t ht δ hδ
  obtain ⟨Q, G, ε0, hε0, hgap, -, hs⟩ := rightData_O75 O t ht
  set s : ℝ := t + min δ ε0 / 2 with hsdef
  have hm : 0 < min δ ε0 := lt_min hδ hε0
  have hts : t < s := by rw [hsdef]; linarith
  have hsε : s ≤ t + ε0 := by rw [hsdef]; linarith [min_le_right δ ε0]
  have hsδ : s < t + δ := by rw [hsdef]; linarith [min_le_left δ ε0]
  have hs0 : 0 < s := ht.trans hts
  have hreg : s ∉ O.eventTimes := fun he => hgap s he hts hsε
  have hpre : (O.observe s hs0.le).time (Fin.last (O.observe s hs0.le).eventCount) < s := by
    apply GC.Surgery.final_time_lt_of_non_event (O.observe s hs0.le) hs0
    intro he
    rw [← O.eventTimes_inter s hs0.le] at he
    exact hreg he.1
  refine ⟨⟨s, hs0, hreg, hpre⟩, hts.le, hsδ, ?_⟩
  obtain ⟨e1, -⟩ := hs t le_rfl (by linarith)
  obtain ⟨e2, -⟩ := hs s hts.le hsε
  exact e1.trans e2.symm

end Observe

end GC.LongTime.Ch12
