import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TrackedTopology_S70
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.FirstFailure_S56

set_option autoImplicit false

/-!
# CH12-S70 / G1d: the active stage as a function of the real time (case split of the closed / open steps)

* `actS_time_le_S70`, `le_actS_S70`, `actS_mono_S70`: the clamped `activeStage` for `r ∈ [0, horizon]`;
* `actS_eq_left_or_event_S70`: at `s > 0`, either `s` is an event time (`time (actS s) = s`) or the active
  stage is constant on a left neighbourhood `[s - ε, s]` (closed step at regular times);
* `exists_actS_eq_right_S70`: for `s < horizon` the active stage is constant on a right neighbourhood
  `[s, s + ε]` (open step; uses `exists_no_event_in_Ioo_S56`);
* `exists_succ_of_time_actS_S70`: an event time `s > 0` (no range hypothesis) is `time i.succ` with `actS s = i.succ`.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem actS_time_le_S70 (K : ObservedHistory.{u}) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) K.horizon) :
    K.time (actS_S70 K r) ≤ r := by
  have h := K.activeStage_time_le (clampT_S70 K r)
  rwa [clampT_val_S70 K hr] at h

theorem le_actS_S70 (K : ObservedHistory.{u}) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) K.horizon)
    {j : Fin (K.eventCount + 1)} (hj : K.time j ≤ r) : j ≤ actS_S70 K r :=
  K.le_activeStage (clampT_S70 K r) j (by rwa [clampT_val_S70 K hr])

theorem actS_mono_S70 (K : ObservedHistory.{u}) {r r' : ℝ} (hr : r ∈ Icc (0 : ℝ) K.horizon)
    (hr' : r' ∈ Icc (0 : ℝ) K.horizon) (h : r ≤ r') : actS_S70 K r ≤ actS_S70 K r' :=
  le_actS_S70 K hr' ((actS_time_le_S70 K hr).trans h)

theorem actS_eq_left_or_event_S70 (K : ObservedHistory.{u}) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) K.horizon) :
    K.time (actS_S70 K s) = s ∨
      ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Icc (s - ε) s, actS_S70 K r = actS_S70 K s := by
  rcases (actS_time_le_S70 K hs).eq_or_lt with h | h
  · exact Or.inl h
  · refine Or.inr ⟨s - K.time (actS_S70 K s), sub_pos.mpr h, fun r hr => ?_⟩
    have hr0 : r ∈ Icc (0 : ℝ) K.horizon :=
      ⟨(K.time_nonneg _).trans (by linarith [hr.1]), hr.2.trans hs.2⟩
    refine le_antisymm (actS_mono_S70 K hr0 hs hr.2) (le_actS_S70 K hr0 ?_)
    linarith [hr.1]

theorem exists_actS_eq_right_S70 (K : ObservedHistory.{u}) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) K.horizon) (hsh : s < K.horizon) :
    ∃ ε : ℝ, 0 < ε ∧ s + ε ≤ K.horizon ∧ ∀ r ∈ Icc s (s + ε), actS_S70 K r = actS_S70 K s := by
  obtain ⟨ε, hε, hno⟩ := exists_no_event_in_Ioo_S56 K s
  refine ⟨min (ε / 2) (K.horizon - s), lt_min (half_pos hε) (sub_pos.mpr hsh),
    by linarith [min_le_right (ε / 2) (K.horizon - s)], fun r hr => ?_⟩
  have hr0 : r ∈ Icc (0 : ℝ) K.horizon := ⟨hs.1.trans hr.1, by
    linarith [hr.2, min_le_right (ε / 2) (K.horizon - s)]⟩
  refine le_antisymm ?_ (actS_mono_S70 K hs hr0 hr.1)
  by_contra hlt
  have hlt' : actS_S70 K s < actS_S70 K r := not_le.mp hlt
  have hle : K.time (actS_S70 K r) ≤ r := actS_time_le_S70 K hr0
  have hgt : s < K.time (actS_S70 K r) := by
    by_contra hnot
    exact absurd (le_actS_S70 K hs (not_lt.mp hnot)) (not_le.mpr hlt')
  exact hno _ ⟨hgt, by linarith [hr.2, min_le_left (ε / 2) (K.horizon - s)]⟩

theorem exists_succ_of_time_actS_S70 (K : ObservedHistory.{u}) {s : ℝ} (hs0 : 0 < s) (h : K.time (actS_S70 K s) = s) :
    ∃ i : Fin K.eventCount, actS_S70 K s = i.succ := by
  have hne : actS_S70 K s ≠ 0 := by
    intro h0
    rw [h0, K.time_zero] at h
    exact hs0.ne h
  exact ⟨(actS_S70 K s).pred hne, (Fin.succ_pred _ _).symm⟩

end GC.LongTime.Ch12
