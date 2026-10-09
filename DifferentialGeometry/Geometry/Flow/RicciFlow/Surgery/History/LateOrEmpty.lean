import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.TowerFinitePrefixes

namespace GC.Surgery
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
set_option autoImplicit false
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem late_prefix_with_initial (T : ObservationTower P g) (B : ℝ) :
    ∃ (t : ℝ) (ht : 0 < t), B < t ∧ t ∉ T.eventTimes ∧
      (T.observe t ht.le).time (Fin.last (T.observe t ht.le).eventCount) < t ∧
      Nonempty (InitialIdentification P g (T.observe t ht.le)) := by
  obtain ⟨t, ht, hB, hn, hs⟩ := regular_prefix_after T B
  exact ⟨t, ht, hB, hn, hs, ⟨T.observeInitial t ht.le⟩⟩

theorem prefix_slice_coherence (T : ObservationTower P g)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) (t : Icc (0 : ℝ) a) :
    (T.observe a ha).stageAt t =
      (T.observe b hb).stageAt ⟨t.1, t.2.1, t.2.2.trans hab⟩ ∧
    HEq ((T.observe a ha).stageMetric ((T.observe a ha).activeStage t) t.1)
      ((T.observe b hb).stageMetric
        ((T.observe b hb).activeStage ⟨t.1, t.2.1, t.2.2.trans hab⟩) t.1) :=
  ⟨T.observe_slice_stage a b ha hb hab t, T.observe_slice_metric a b ha hb hab t⟩

theorem late_nonempty_or_absorbing_empty (T : ObservationTower P g) :
    (∃ (a : ℝ) (_ha : 0 ≤ a),
      (∀ (b : ℝ) (hb : 0 ≤ b), a ≤ b →
        IsEmpty ((T.observe b hb).stage (Fin.last (T.observe b hb).eventCount)).Carrier) ∧
      (∀ s ∈ T.eventTimes, s ≤ a)) ∨
    (∀ B : ℝ, ∃ (t : ℝ) (ht : 0 < t), B < t ∧ t ∉ T.eventTimes ∧
      (T.observe t ht.le).time (Fin.last (T.observe t ht.le).eventCount) < t ∧
      Nonempty ((T.observe t ht.le).stage (Fin.last (T.observe t ht.le).eventCount)).Carrier) := by
  classical
  by_cases h : ∃ (a : ℝ) (ha : 0 ≤ a),
      IsEmpty ((T.observe a ha).stage (Fin.last (T.observe a ha).eventCount)).Carrier
  · obtain ⟨a, ha, hempty⟩ := h
    let := hempty
    exact Or.inl ⟨a, ha, (fun b hb hab => T.empty_absorbing a b ha hb hab),
      T.empty_no_later_events a ha⟩
  · right
    intro B
    obtain ⟨t, ht, hB, hn, hs⟩ := regular_prefix_after T B
    refine ⟨t, ht, hB, hn, hs, ?_⟩
    by_contra he
    exact h ⟨t, ht.le, not_nonempty_iff.mp he⟩

theorem no_event_strictly_after_empty (T : ObservationTower P g)
    (a : ℝ) (ha : 0 ≤ a)
    [IsEmpty ((T.observe a ha).stage (Fin.last (T.observe a ha).eventCount)).Carrier]
    (t : ℝ) (hat : a < t) : t ∉ T.eventTimes := by
  intro he
  exact (not_lt_of_ge (T.empty_no_later_events a ha t he)) hat

end GC.Surgery
