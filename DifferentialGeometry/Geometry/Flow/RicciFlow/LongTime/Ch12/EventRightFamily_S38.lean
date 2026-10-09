import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyCoresPost_S37

set_option autoImplicit false

/-!
# CH12-S38 / G2 glue: a smooth right family at an event time

At an event time `te` of an observation tower, the post-surgery stage and metric are the value
at `te` of a single smooth family `G` on a fixed stage `Q` (the last stage of a slightly later
observed history), and every regular slice just after `te` has stage `Q` and metric `G (time)`.
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

/-- `postStage`/`postMetric` at a nonnegative time are the last stage/metric of `observe`. -/
theorem postStage_eq_observe_S38 (t : ℝ) (ht : 0 ≤ t) :
    postStage O t = (O.observe t ht).stage (Fin.last (O.observe t ht).eventCount) ∧
      HEq (postMetric O t) ((O.observe t ht).stageMetric (Fin.last (O.observe t ht).eventCount) t) := by
  have htime : max t 0 = t := max_eq_left ht
  have hobs : O.observe (max t 0) (le_max_right t 0) = O.observe t ht := by
    have hsub : (⟨max t 0, le_max_right t 0⟩ : {t : ℝ // 0 ≤ t}) = ⟨t, ht⟩ := Subtype.ext htime
    exact congrArg (fun t : {t : ℝ // 0 ≤ t} => O.observe t.val t.property) hsub
  have hmetric : ∀ {H H' : ObservedHistory}, H = H' → ∀ t : ℝ,
      HEq (H.stageMetric (Fin.last H.eventCount) t) (H'.stageMetric (Fin.last H'.eventCount) t) := by
    intro H H' h t
    cases h
    rfl
  refine ⟨congrArg (fun H : ObservedHistory => H.stage (Fin.last H.eventCount)) hobs, ?_⟩
  exact (heq_of_eq (congrArg
    (fun τ => (O.observe (max t 0) (le_max_right t 0)).stageMetric
      (Fin.last (O.observe (max t 0) (le_max_right t 0)).eventCount) τ)
    htime)).trans (hmetric hobs t)


/-- Comparison of the last stage and metric of `observe a` with those of `observe b` (`a ≤ b`),
when the last stage of `observe b` is already active at time `a` and has begun before `b`. -/
theorem observe_last_eq_S38 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b)
    (hk : (O.observe b hb).activeStage ⟨a, ha, hab⟩ = Fin.last (O.observe b hb).eventCount)
    (hlt : (O.observe b hb).time (Fin.last (O.observe b hb).eventCount) < b) :
    ∃ _ : (O.observe a ha).stage (Fin.last (O.observe a ha).eventCount) =
        (O.observe b hb).stage (Fin.last (O.observe b hb).eventCount),
      ∀ τ : ℝ, (O.observe b hb).time (Fin.last (O.observe b hb).eventCount) ≤ τ → τ ≤ a →
        HEq ((O.observe a ha).stageMetric (Fin.last (O.observe a ha).eventCount) τ)
          ((O.observe b hb).stageMetric (Fin.last (O.observe b hb).eventCount) τ) := by
  have R := O.observe_restrict a b ha hb hab
  set HB := O.observe b hb with hHB
  set HA := O.observe a ha with hHA
  set HR := HB.restrict ⟨a, ha, hab⟩ with hHR
  have hfin1 : Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last HR.eventCount) =
      Fin.last HA.eventCount := Fin.ext R.count_eq
  have hfin2 : (Fin.castLE (Nat.add_le_add_right
      (Nat.le_of_lt_succ (HB.activeStage ⟨a, ha, hab⟩).isLt) 1) (Fin.last HR.eventCount)) =
      Fin.last HB.eventCount := by
    exact Fin.ext (congrArg Fin.val hk)
  refine ⟨?_, ?_⟩
  · have h1 := R.stage_eq (Fin.last HR.eventCount)
    rw [hfin1] at h1
    exact h1.symm.trans (congrArg HB.stage hfin2)
  · intro τ hτ1 hτ2
    have hdom : τ ∈ HR.stageDomain (Fin.last HR.eventCount) := by
      simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
      refine ⟨?_, hτ2⟩
      have : HR.time (Fin.last HR.eventCount) = HB.time (Fin.last HB.eventCount) :=
        congrArg HB.time hfin2
      rw [this]
      exact hτ1
    have h1 := R.metric_heq (Fin.last HR.eventCount) τ hdom
    rw [hfin1] at h1
    refine h1.symm.trans ?_
    have hlt2 : HB.time (Fin.last HB.eventCount) < HB.horizon := hlt
    have hfs : HB.stageMetric (Fin.last HB.eventCount) τ = (HB.finalSlab hlt).flow.base.metric τ := by
      simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hlt2]
    by_cases hlt' : HR.time (Fin.last HR.eventCount) < HR.horizon
    · have e1 : HEq (HR.stageMetric (Fin.last HR.eventCount) τ)
          (HB.stageMetric (HB.activeStage ⟨a, ha, hab⟩) τ) := by
        rw [← HB.closedPrefixAt_metric ⟨a, ha, hab⟩ hlt' τ]
        apply heq_of_eq
        simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hlt']
        rfl
      exact e1.trans (congr_arg_heq (fun j => HB.stageMetric j τ) hk)
    · have hτa : τ = HB.time (Fin.last HB.eventCount) := by
        have h0 : HR.time (Fin.last HR.eventCount) = HB.time (Fin.last HB.eventCount) :=
          congrArg HB.time hfin2
        have h3 : a ≤ HR.time (Fin.last HR.eventCount) := not_lt.mp hlt'
        have h4 : τ ≤ a := hτ2
        linarith
      have e2 : HEq (HR.stageMetric (Fin.last HR.eventCount) τ)
          (HB.initialMetric (Fin.last HB.eventCount)) := by
        simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_right hlt']
        exact (heq_of_eq rfl : HEq (HR.initialMetric (Fin.last HR.eventCount))
          (HB.initialMetric (Fin.castLE _ (Fin.last HR.eventCount)))).trans
          (congr_arg_heq (fun j => HB.initialMetric j) hfin2)
      refine e2.trans (heq_of_eq ?_)
      rw [hfs, hτa]
      exact (HB.final_initial hlt).symm


/-- There is a gap after an event time with no further event. -/
theorem exists_eventFree_gap_S38 {te : ℝ} :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ 1 ∧ ∀ s ∈ O.eventTimes, te < s → s ≤ te + ε0 → False := by
  have hfin := O.eventTimes_finite_Icc te (te + 1)
  set S : Set ℝ := {s | s ∈ O.eventTimes ∧ te < s ∧ s ≤ te + 1} with hS
  have hSfin : S.Finite := hfin.subset (fun s hs => ⟨hs.1, hs.2.1.le, hs.2.2⟩)
  by_cases hne : S.Nonempty
  · obtain ⟨m, hm, hmin⟩ := Set.exists_min_image S id hSfin hne
    refine ⟨min 1 ((m - te) / 2), lt_min one_pos (by linarith [hm.2.1]), min_le_left _ _, ?_⟩
    intro s hs h1 h2
    have hs1 : s ≤ te + 1 := h2.trans (by linarith [min_le_left 1 ((m - te) / 2)])
    have := hmin s ⟨hs, h1, hs1⟩
    simp only [id] at this
    have h3 : s ≤ te + (m - te) / 2 := h2.trans (by linarith [min_le_right 1 ((m - te) / 2)])
    linarith [hm.2.1]
  · refine ⟨1, one_pos, le_rfl, ?_⟩
    intro s hs h1 h2
    exact hne ⟨s, hs, h1, h2⟩

/-- **GLUE.**  At an event time `te`, the post-surgery stage and metric are the value at `te` of one
smooth family `G` on a fixed stage `Q`, and every regular slice in `(te, te + ε0]` has stage `Q` and
metric `G (time)`. -/
theorem exists_smooth_right_family_S38 {te : ℝ} (hte : te ∈ O.eventTimes) :
    ∃ (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric) (ε0 : ℝ), 0 < ε0 ∧
      Q.MetricSmoothUpTo G (Icc te (te + ε0)) ∧ postStage O te = Q ∧
      HEq (postMetric O te) (G te) ∧
      ∀ s : RegularSlice O, te < s.time → s.time ≤ te + ε0 → s.stage = Q ∧ HEq s.metric (G s.time) := by
  have hte0 : 0 < te := O.eventTimes_pos hte
  obtain ⟨ε0, hε0, hε1, hgap⟩ := exists_eventFree_gap_S38 O (te := te)
  have hb : 0 ≤ te + ε0 := by linarith
  set HB := O.observe (te + ε0) hb with hHB
  have hEv : HB.eventTimes = O.eventTimes ∩ Ioc 0 (te + ε0) := (O.eventTimes_inter _ hb).symm
  -- the last stage of `HB` starts exactly at `te`
  have htl : HB.time (Fin.last HB.eventCount) = te := by
    have hte' : te ∈ HB.eventTimes := by
      rw [hEv]; exact ⟨hte, hte0, by linarith⟩
    obtain ⟨i, hi⟩ := hte'
    have h1 : te ≤ HB.time (Fin.last HB.eventCount) :=
      hi ▸ HB.time_strictMono.monotone (Fin.le_last _)
    refine le_antisymm ?_ h1
    rcases Fin.eq_zero_or_eq_succ (Fin.last HB.eventCount) with h0 | ⟨j, hj⟩
    · rw [h0, HB.time_zero]; exact hte0.le
    · have hmem : HB.time (Fin.last HB.eventCount) ∈ HB.eventTimes := ⟨j, hj ▸ rfl⟩
      rw [hEv] at hmem
      by_contra hcon
      exact hgap _ hmem.1 (not_le.mp hcon) hmem.2.2
  have hlt : HB.time (Fin.last HB.eventCount) < te + ε0 := by rw [htl]; linarith
  have hlt2 : HB.time (Fin.last HB.eventCount) < HB.horizon := hlt
  have hfs : ∀ τ, HB.stageMetric (Fin.last HB.eventCount) τ = (HB.finalSlab hlt).flow.base.metric τ := by
    intro τ
    simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hlt2]
  have hsmooth : (HB.stage (Fin.last HB.eventCount)).MetricSmoothUpTo
      (HB.stageMetric (Fin.last HB.eventCount)) (Icc te (te + ε0)) := by
    have hG : HB.stageMetric (Fin.last HB.eventCount) = (HB.finalSlab hlt).flow.base.metric :=
      funext hfs
    rw [hG]
    refine (HB.finalSlab hlt).smoothUpTo.mono ?_
    intro x hx
    exact ⟨by rw [htl]; exact hx.1, hx.2⟩
  have hk : ∀ a (ha : 0 ≤ a) (hab : a ≤ te + ε0), te ≤ a →
      HB.activeStage ⟨a, ha, hab⟩ = Fin.last HB.eventCount := fun a ha hab hta =>
    le_antisymm (Fin.le_last _) (HB.le_activeStage _ _ (htl.le.trans hta))
  refine ⟨HB.stage (Fin.last HB.eventCount), HB.stageMetric (Fin.last HB.eventCount), ε0, hε0,
    hsmooth, ?_, ?_, ?_⟩
  · obtain ⟨e, -⟩ := observe_last_eq_S38 O te (te + ε0) hte0.le hb (by linarith)
      (hk te hte0.le (by linarith) le_rfl) hlt
    exact (postStage_eq_observe_S38 O te hte0.le).1.trans e
  · obtain ⟨-, hm⟩ := observe_last_eq_S38 O te (te + ε0) hte0.le hb (by linarith)
      (hk te hte0.le (by linarith) le_rfl) hlt
    exact (postStage_eq_observe_S38 O te hte0.le).2.trans (hm te htl.le le_rfl)
  · intro s hs1 hs2
    obtain ⟨e, hm⟩ := observe_last_eq_S38 O s.time (te + ε0) s.positive.le hb hs2
      (hk s.time s.positive.le hs2 hs1.le) hlt
    exact ⟨e, hm s.time (htl.le.trans hs1.le) le_rfl⟩

end Observe

end GC.LongTime.Ch12
