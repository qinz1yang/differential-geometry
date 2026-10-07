import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceSeeds_CX2

/-!
# CH12-S74: regular times of the slice's tower history (R4 D-R4-5 (1))

`regular_iff_not_mem_eventTimes_S74`: for a positive time `u` of an observed history `H`,
`H.time (H.activeStage u) < u ↔ u ∉ H.eventTimes`.
`regular_iff_slice_S74`: for `0 < u ≤ s.time` and `N := sliceTowerHistory_CX2 s`,
`N.time (N.activeStage u) < u ↔ u ∉ F.observation.eventTimes` (prefix hypothesis `u ≤ s.time`:
the event times of the tower observation in `(0, s.time]` are those of `N`).
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

theorem regular_iff_not_mem_eventTimes_S74 {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    (ht : 0 < (t : ℝ)) :
    H.time (H.activeStage t) < (t : ℝ) ↔ (t : ℝ) ∉ H.eventTimes := by
  constructor
  · rintro hlt ⟨j, hj⟩
    have h1 : j.succ ≤ H.activeStage t := H.le_activeStage t _ hj.le
    have h2 := H.time_strictMono.monotone h1
    have hj' : H.time j.succ = (t : ℝ) := hj
    rw [hj'] at h2
    exact absurd h2 (not_le.mpr hlt)
  · intro hne
    refine lt_of_le_of_ne (H.activeStage_time_le t) (fun heq => hne ?_)
    have hne0 : H.activeStage t ≠ 0 := fun h0 => by
      rw [h0, H.time_zero] at heq
      linarith
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hne0
    exact ⟨j, by
      change H.time j.succ = (t : ℝ)
      rw [hj]; exact heq⟩

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

theorem mem_eventTimes_slice_iff_S74 {s : RegularSlice F.observation}
    {t : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon} (ht : 0 < (t : ℝ))
    (hts : (t : ℝ) ≤ s.time) :
    (t : ℝ) ∈ F.observation.eventTimes ↔ (t : ℝ) ∈ (sliceTowerHistory_CX2 s).eventTimes := by
  have h1 := F.observation.eventTimes_inter s.time s.positive.le
  have h2 := (sliceTowerHistory_CX2 s).restrict_eventTimes (sliceTowerTime_CX2 s)
  have hmem : (t : ℝ) ∈ Ioc 0 s.time := ⟨ht, hts⟩
  constructor
  · intro h
    have h3 : (t : ℝ) ∈ F.observation.eventTimes ∩ Ioc 0 s.time := ⟨h, hmem⟩
    rw [h1] at h3
    have h4 : (t : ℝ) ∈ ((sliceTowerHistory_CX2 s).restrict (sliceTowerTime_CX2 s)).eventTimes := h3
    rw [h2] at h4
    exact h4.1
  · intro h
    have h4 : (t : ℝ) ∈ ((sliceTowerHistory_CX2 s).restrict (sliceTowerTime_CX2 s)).eventTimes := by
      rw [h2]
      exact ⟨h, hmem⟩
    have h3 : (t : ℝ) ∈ (F.observation.observe s.time s.positive.le).eventTimes := h4
    rw [← h1] at h3
    exact h3.1

theorem regular_iff_slice_S74 {s : RegularSlice F.observation}
    {t : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon} (ht : 0 < (t : ℝ))
    (hts : (t : ℝ) ≤ s.time) :
    (sliceTowerHistory_CX2 s).time ((sliceTowerHistory_CX2 s).activeStage t) < (t : ℝ) ↔
      (t : ℝ) ∉ F.observation.eventTimes := by
  rw [regular_iff_not_mem_eventTimes_S74 ht]
  exact not_congr (mem_eventTimes_slice_iff_S74 ht hts).symm

end GC.LongTime.Ch12
