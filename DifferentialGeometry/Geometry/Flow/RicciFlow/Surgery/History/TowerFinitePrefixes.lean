import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ObservationTower
import Mathlib.Order.Interval.Set.Infinite

namespace GC.Surgery
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
set_option autoImplicit false
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem finite_prefix_exact (T : ObservationTower P g) (b : ℝ) (hb : 0 ≤ b) :
    (T.observe b hb).eventTimes = T.eventTimes ∩ Ioc 0 b ∧
      (T.eventTimes ∩ Ioc 0 b).Finite :=
  ⟨(T.eventTimes_inter b hb).symm, T.eventTimes_finite b hb⟩

theorem non_event_time_after (T : ObservationTower P g) (B : ℝ) :
    ∃ t : ℝ, max B 0 < t ∧ t < max B 0 + 1 ∧ t ∉ T.eventTimes := by
  obtain ⟨t, ht, hn⟩ := (Ioo_infinite (show max B 0 < max B 0 + 1 by linarith)).exists_notMem_finite
    (T.eventTimes_finite_Icc (max B 0) (max B 0 + 1))
  exact ⟨t, ht.1, ht.2, fun he => hn ⟨he, ht.1.le, ht.2.le⟩⟩

theorem final_time_lt_of_non_event (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (hn : H.horizon ∉ H.eventTimes) :
    H.time (Fin.last H.eventCount) < H.horizon := by
  apply lt_of_le_of_ne H.time_le_horizon
  intro he
  by_cases hc : H.eventCount = 0
  · have hf : Fin.last H.eventCount = 0 := Fin.ext (by simpa using hc)
    rw [hf, H.time_zero] at he
    exact (ne_of_gt hpos) he.symm
  · let i : Fin H.eventCount := ⟨H.eventCount - 1, by omega⟩
    have hi : i.succ = Fin.last H.eventCount := Fin.ext (by dsimp [i]; omega)
    apply hn
    exact ⟨i, by change H.time i.succ = H.horizon; rw [hi, he]⟩

theorem regular_prefix_after (T : ObservationTower P g) (B : ℝ) :
    ∃ (t : ℝ) (ht : 0 < t), B < t ∧ t ∉ T.eventTimes ∧
      (T.observe t ht.le).time (Fin.last (T.observe t ht.le).eventCount) < t := by
  obtain ⟨t, ht, _, hn⟩ := non_event_time_after T B
  have hp : 0 < t := (le_max_right B 0).trans_lt ht
  refine ⟨t, hp, (le_max_left B 0).trans_lt ht, hn, ?_⟩
  apply final_time_lt_of_non_event (T.observe t hp.le) hp
  intro he
  rw [← T.eventTimes_inter t hp.le] at he
  exact hn he.1

noncomputable def selectedFinalSlab (T : ObservationTower P g) (B : ℝ) :
    let t := Classical.choose (regular_prefix_after T B)
    let ht := Classical.choose (Classical.choose_spec (regular_prefix_after T B))
    ((T.observe t ht.le).stage (Fin.last (T.observe t ht.le).eventCount)).ClosedSlab
      ((T.observe t ht.le).time (Fin.last (T.observe t ht.le).eventCount)) t := by
  dsimp
  exact (T.observe _ _).finalSlab
    (Classical.choose_spec (Classical.choose_spec (regular_prefix_after T B))).2.2

end GC.Surgery
