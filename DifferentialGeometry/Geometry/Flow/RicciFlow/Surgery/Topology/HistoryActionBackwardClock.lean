import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction
set_option autoImplicit false
noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem regularizedStage_endpoint_clocks
    {first last : Fin (H.eventCount + 1)} {T u v : ℝ}
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (huv : u ≤ v) (hu : 0 ≤ u)
    (j : H.StageInterval first last) :
    T - (H.regularizedStageStart T u j.val) ^ 2 = min (T - u ^ 2) (H.stageEndTime j.val) ∧
    T - (H.regularizedStageEnd T v j.val) ^ 2 = max (T - v ^ 2) (H.time j.val) := by
  have htime : H.time j.val ≤ T - u ^ 2 :=
    (H.time_strictMono.monotone j.property.2).trans hupper.1
  have hstart : 0 ≤ T - min (T - u ^ 2) (H.stageEndTime j.val) := by
    have := min_le_left (T - u ^ 2) (H.stageEndTime j.val)
    linarith [sq_nonneg u]
  have hend : 0 ≤ T - max (T - v ^ 2) (H.time j.val) := by
    have : max (T - v ^ 2) (H.time j.val) ≤ T - u ^ 2 :=
      max_le (sub_le_sub_left (sq_le_sq₀ hu (hu.trans huv) |>.2 huv) T) htime
    linarith [sq_nonneg u]
  simp only [regularizedStageStart, regularizedStageEnd, Real.sq_sqrt hstart, Real.sq_sqrt hend,
    sub_sub_cancel, and_self]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false

noncomputable section
open Set
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u})

theorem mapsTo_regularizedStage_Ioo_Ioo (T u v : ℝ) (j : Fin (H.eventCount + 1)) :
    MapsTo (fun t : ℝ => T - t ^ 2)
      (Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j))
      (Ioo (H.time j) (H.stageEndTime j)) := by
  intro t ht
  have ht0 : 0 ≤ t := (Real.sqrt_nonneg _).trans ht.1.le
  have hlo : T - min (T - u ^ 2) (H.stageEndTime j) < t ^ 2 := by
    have hnn : 0 ≤ T - min (T - u ^ 2) (H.stageEndTime j) := by
      have hh := min_le_left (T - u ^ 2) (H.stageEndTime j)
      linarith [sq_nonneg u]
    exact (Real.sqrt_lt hnn ht0).mp ht.1
  have hhi : t ^ 2 < T - max (T - v ^ 2) (H.time j) := (Real.lt_sqrt ht0).mp ht.2
  constructor
  · have hjmax := le_max_right (T - v ^ 2) (H.time j)
    linarith
  · have hminend := min_le_right (T - u ^ 2) (H.stageEndTime j)
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

noncomputable section
open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem eventually_mem_stageDomain_of_backward_clock_mem_Ioo
    (j : Fin (H.eventCount + 1)) {T v : ℝ}
    (hv : T - v ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j)) :
    ∀ᶠ w in 𝓝 v, T - w ^ 2 ∈ H.stageDomain j := by
  have hc : ContinuousAt (fun w : ℝ => T - w ^ 2) v :=
    continuousAt_const.sub (continuousAt_id.pow 2)
  filter_upwards [hc.eventually (Ioo_mem_nhds hv.1 hv.2)] with w hw
  exact H.mem_stageDomain_of_mem_Ioo hw

theorem eventually_activeStage_eq_of_backward_clock_mem_Ioo
    (j : Fin (H.eventCount + 1)) {T v : ℝ}
    (hv : T - v ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j)) :
    ∀ᶠ w in 𝓝 v, ∀ hw : T - w ^ 2 ∈ Icc 0 H.horizon,
      H.activeStage ⟨T - w ^ 2, hw⟩ = j := by
  filter_upwards [H.eventually_mem_stageDomain_of_backward_clock_mem_Ioo j hv] with w hw
  intro hrange
  exact (H.mem_stageDomain_iff ⟨T - w ^ 2, hrange⟩ j).mp hw

theorem eventually_activeStage_eq_of_backward_clock_event
    (i : Fin H.eventCount) {T v : ℝ} (hv : 0 < v)
    (hevent : T - v ^ 2 = H.time i.succ) :
    ∀ᶠ w in 𝓝 v, ∀ hw : T - w ^ 2 ∈ Icc 0 H.horizon,
      H.activeStage ⟨T - w ^ 2, hw⟩ = if w ≤ v then i.succ else i.castSucc := by
  have hc : ContinuousAt (fun w : ℝ => T - w ^ 2) v :=
    continuousAt_const.sub (continuousAt_id.pow 2)
  have hlo : ∀ᶠ w in 𝓝 v, H.time i.castSucc < T - w ^ 2 :=
    hc.eventually_const_lt (by
      change H.time i.castSucc < T - v ^ 2
      rw [hevent]
      exact H.time_strictMono i.castSucc_lt_succ)
  have hnew : ∀ᶠ w in 𝓝 v, ∀ hw : T - w ^ 2 ∈ Icc 0 H.horizon,
      H.time i.succ ≤ T - w ^ 2 → T - w ^ 2 ∈ H.stageDomain i.succ := by
    rcases Fin.eq_castSucc_or_eq_last i.succ with ⟨j, hj⟩ | hj
    · have hbound : T - v ^ 2 < H.time j.succ := by
        rw [hevent, hj]
        exact H.time_strictMono j.castSucc_lt_succ
      filter_upwards [hc.eventually_lt_const hbound] with w hw
      intro hrange hle
      rw [hj, stageDomain, Fin.lastCases_castSucc]
      exact ⟨hj ▸ hle, hw⟩
    · filter_upwards [] with w
      intro hrange hle
      rw [hj, stageDomain, Fin.lastCases_last]
      exact ⟨hj ▸ hle, hrange.2⟩
  filter_upwards [eventually_gt_nhds hv, hlo, hnew] with w hwpos hwlo hwnew
  intro hrange
  split_ifs with hwv
  · apply (H.mem_stageDomain_iff ⟨T - w ^ 2, hrange⟩ i.succ).mp
    apply hwnew hrange
    have hsq := pow_le_pow_left₀ hwpos.le hwv 2
    linarith
  · apply (H.mem_stageDomain_iff ⟨T - w ^ 2, hrange⟩ i.castSucc).mp
    rw [stageDomain, Fin.lastCases_castSucc]
    refine ⟨hwlo.le, ?_⟩
    have hsq : v ^ 2 < w ^ 2 := by nlinarith [lt_of_not_ge hwv]
    linarith

theorem eventually_activeStage_eq_zero_of_backward_clock_eq_zero
    {T v : ℝ} (hv : T - v ^ 2 = 0) :
    ∀ᶠ w in 𝓝 v, ∀ hw : T - w ^ 2 ∈ Icc 0 H.horizon,
      H.activeStage ⟨T - w ^ 2, hw⟩ = 0 := by
  rcases Nat.eq_zero_or_pos H.eventCount with hzero | hpos
  · filter_upwards [] with w
    intro hrange
    apply Fin.ext
    have hbound := (H.activeStage ⟨T - w ^ 2, hrange⟩).isLt
    simp only [hzero] at hbound
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hbound)
  · let i : Fin H.eventCount := ⟨0, hpos⟩
    have hi : i.castSucc = 0 := Fin.ext rfl
    have hc : ContinuousAt (fun w : ℝ => T - w ^ 2) v :=
      continuousAt_const.sub (continuousAt_id.pow 2)
    have hbound : T - v ^ 2 < H.time i.succ := by
      rw [hv, ← H.time_zero, ← hi]
      exact H.time_strictMono i.castSucc_lt_succ
    filter_upwards [hc.eventually_lt_const hbound] with w hw
    intro hrange
    apply (H.mem_stageDomain_iff ⟨T - w ^ 2, hrange⟩ 0).mp
    rw [← hi, stageDomain, Fin.lastCases_castSucc]
    exact ⟨by simpa only [hi, H.time_zero] using hrange.1, hw⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
