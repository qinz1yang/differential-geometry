import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MatchedRawScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction

set_option autoImplicit false

/-!
# CX-SPINE G21：固定种子归一化下的 actual record scale 分离

直接消费已证明的 recent nominal/recenter 叶子；不重新证明其18C尺度界。
nr(t)≤r 与 M*r²≤L（L 在 queries 之前固定）给 4M<static scale。
事件只需在 [t/2,t]，包括终端 birth；native 小种子分支不由本结论支付。
-/

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology

open private GC.GeneralFlow.eventually_matched_raw_scale_on_history_family from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MatchedRawScale

namespace GC.LongTime.Ch11

universe u

/-- 同一 actual records family 的固定 seed-scale gap；阈值先于全部 queries。 -/
theorem exists_late_seed_record_scale_CXSP
    (histories : ℕ → ObservedHistory.{u}) (params : CutoffParameters)
    (records : ∀ n, ∀ e : Fin (histories n).eventCount,
      GeometricCutoffRecord (histories n) e params)
    (hdecay : Tendsto params.delta atTop (𝓝 0))
    (hrecent : ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (histories n).eventCount,
        (histories n).time e.succ ∈ Icc (t / 2) t →
        ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t)
    (L : ℝ) :
    ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (t : ℝ), T₀ ≤ t → ∀ n : ℕ, ∀ e : Fin (histories n).eventCount,
        (histories n).time e.succ ∈ Icc (t / 2) t →
        ∀ (r M : ℝ), 0 < r → params.neckRadius t ≤ r → M * r ^ 2 ≤ L →
        ∀ b, 4 * M < ((records n e).static b).neck.scale := by
  let C := max 1 L
  have hC : 1 ≤ C := le_max_left _ _
  obtain ⟨T₀, hT₀, hscale⟩ := GC.GeneralFlow.eventually_matched_raw_scale_on_history_family
    histories params records hdecay hrecent C hC
  refine ⟨T₀, hT₀, ?_⟩
  intro t ht n e he r M hr hnr hML b
  have hnrpos := params.neckRadius_pos t (hT₀.trans_le ht).le
  have hQ : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
  have hQnr : (r ^ 2)⁻¹ ≤ (params.neckRadius t ^ 2)⁻¹ :=
    (inv_le_inv₀ (sq_pos_of_pos hr) (sq_pos_of_pos hnrpos)).mpr
      (pow_le_pow_left₀ hnrpos.le hnr 2)
  have hsep := hscale t ht n e he ((records n e).static b) rfl (r ^ 2)⁻¹ hQ hQnr
  have hMC : M ≤ C * (r ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos hr)]
    exact hML.trans (le_max_right _ _)
  have hCQ : 0 < C * (r ^ 2)⁻¹ := mul_pos (zero_lt_one.trans_le hC) hQ
  nlinarith

/-- 实际 crossed events 位于候选窗口之后；后半窗足以满足 recent 的闭区间条件。 -/
theorem crossed_event_mem_half_window_CXSP
    (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon}
    (hhalf : (t : ℝ) / 2 ≤ a) (e : Fin H.eventCount)
    (hf : H.activeStage a ≤ e.castSucc) (hl : e.succ ≤ H.activeStage t) :
    H.time e.succ ∈ Icc ((t : ℝ) / 2) t := by
  have hae : (a : ℝ) < H.time e.succ := by
    by_contra h
    have he := H.le_activeStage a e.succ (le_of_not_gt h)
    exact (not_le_of_gt e.castSucc_lt_succ) (he.trans hf)
  exact ⟨hhalf.trans hae.le,
    (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)⟩

end GC.LongTime.Ch11
