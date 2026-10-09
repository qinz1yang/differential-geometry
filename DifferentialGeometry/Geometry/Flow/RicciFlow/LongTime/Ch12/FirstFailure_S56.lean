import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

set_option autoImplicit false

/-!
# CH12-S56 / G2: the first-failure (continuity) argument, order-theoretic core

`first_failure_bootstrap_S56` is the real-induction scheme behind the `[t, 2t]` forward window of
`hLTF04`: `Strong s` is the improved estimate (defect `≤ η/2`, curvature `≤ C/s`, ...), `Weak s` the
a-priori estimate (defect `≤ η`, curvature `≤ 2C/s`, ball survives).  The three geometric steps are
* `hclosed`: `Weak` on `[a, s)` gives `Weak s` (limit of the flow data, and passage through an event
  by the anchored survivor map `survivor_chart_of_flow_scalar_S56`),
* `hopen`: `Strong s` gives `Weak` on `[s, s+ε]` (continuity of the smooth flow between events;
  `exists_no_event_in_Ioo_S56` supplies `ε` below the next event time),
* `himprove`: `Weak` on `[a, s]` gives `Strong s` (LTF03 at the regular slices, `ltf03_vector_threshold_S45`,
  plus `metric_variation_S45` for the seed).
Then no first failure time exists.
-/

open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

/-- No first failure time: real induction with an a-priori (`Weak`) / improved (`Strong`) pair. -/
theorem first_failure_bootstrap_S56 {a b : ℝ} (hab : a ≤ b) (Strong Weak : ℝ → Prop)
    (h0 : Strong a) (hSW : ∀ s, Strong s → Weak s)
    (hclosed : ∀ s ∈ Ioc a b, (∀ r ∈ Ico a s, Weak r) → Weak s)
    (hopen : ∀ s ∈ Ico a b, Strong s → ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Icc s (s + ε), Weak r)
    (himprove : ∀ s ∈ Icc a b, (∀ r ∈ Icc a s, Weak r) → Strong s) :
    ∀ s ∈ Icc a b, Strong s := by
  classical
  let S : Set ℝ := {s | s ∈ Icc a b ∧ ∀ r ∈ Icc a s, Weak r}
  have haS : a ∈ S := by
    refine ⟨⟨le_rfl, hab⟩, fun r hr => ?_⟩
    rw [le_antisymm hr.2 hr.1]
    exact hSW a h0
  have hne : S.Nonempty := ⟨a, haS⟩
  have hbdd : BddAbove S := ⟨b, fun s hs => hs.1.2⟩
  have hmax : ∀ s ∈ S, s ≤ sSup S := fun s hs => le_csSup hbdd hs
  have hlt' : ∀ r < sSup S, ∃ s ∈ S, r < s := fun r hr => exists_lt_of_lt_csSup hne hr
  have hac : a ≤ sSup S := hmax a haS
  have hcb : sSup S ≤ b := csSup_le hne fun s hs => hs.1.2
  generalize sSup S = c at hmax hlt' hac hcb
  have hlt : ∀ r ∈ Ico a c, Weak r := fun r hr => by
    obtain ⟨s, hsS, hrs⟩ := hlt' r hr.2
    exact hsS.2 r ⟨hr.1, hrs.le⟩
  have hWc : Weak c := by
    rcases hac.eq_or_lt with h | h
    · rw [← h]
      exact hSW a h0
    · exact hclosed c ⟨h, hcb⟩ hlt
  have hcS : c ∈ S := by
    refine ⟨⟨hac, hcb⟩, fun r hr => ?_⟩
    rcases hr.2.eq_or_lt with h | h
    · rw [h]
      exact hWc
    · exact hlt r ⟨hr.1, h⟩
  have hStrongc : Strong c := himprove c ⟨hac, hcb⟩ hcS.2
  have hcb' : c = b := by
    by_contra hne'
    have hclt : c < b := lt_of_le_of_ne hcb hne'
    obtain ⟨ε, hε, hW⟩ := hopen c ⟨hac, hclt⟩ hStrongc
    have hmem : min (c + ε) b ∈ S := by
      refine ⟨⟨le_min (by linarith) hab, min_le_right _ _⟩, fun r hr => ?_⟩
      rcases le_or_gt r c with h | h
      · exact hcS.2 r ⟨hr.1, h⟩
      · exact hW r ⟨h.le, hr.2.trans (min_le_left _ _)⟩
    have h1 := hmax _ hmem
    have h2 : c < min (c + ε) b := lt_min (by linarith) hclt
    linarith
  intro s hs
  refine himprove s hs fun r hr => ?_
  rw [hcb'] at hcS
  exact hcS.2 r ⟨hr.1, hr.2.trans hs.2⟩

/-- Between two event times there is room: an observed history has no event time in
`(s, s + ε)` for small `ε > 0` (finitely many events). -/
theorem exists_no_event_in_Ioo_S56 (H : ObservedHistory.{u}) (s : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j : Fin (H.eventCount + 1), H.time j ∉ Ioo s (s + ε) := by
  classical
  by_cases h : ∃ j : Fin (H.eventCount + 1), s < H.time j
  · obtain ⟨j, hj⟩ := h
    obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun j : Fin (H.eventCount + 1) => s < H.time j) H.time
      ⟨j, by simpa using hj⟩
    have hj₀s : s < H.time j₀ := by simpa using hj₀
    refine ⟨H.time j₀ - s, sub_pos.mpr hj₀s, fun k hk => ?_⟩
    have := hmin k (by simpa using hk.1)
    linarith [hk.2]
  · refine ⟨1, one_pos, fun k hk => h ⟨k, hk.1⟩⟩

/-- Forward window form: on the closed interval `[s, s + ε]` the active stage cannot change inside
`(s, s+ε)`, i.e. the next event after `s` happens at time `≥ s + ε`. -/
theorem exists_no_event_in_Ioo_of_lt_S56 (H : ObservedHistory.{u}) (s : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j : Fin (H.eventCount + 1), s < H.time j → s + ε ≤ H.time j := by
  obtain ⟨ε, hε, h⟩ := exists_no_event_in_Ioo_S56 H s
  refine ⟨ε, hε, fun j hj => ?_⟩
  by_contra hlt
  exact h j ⟨hj, not_le.mp hlt⟩

end GC.LongTime.Ch12
