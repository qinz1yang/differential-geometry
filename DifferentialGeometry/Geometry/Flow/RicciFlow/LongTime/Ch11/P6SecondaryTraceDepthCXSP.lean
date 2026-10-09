import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedUniformTraceWindowCXSP

set_option autoImplicit false

/-!
# CX-SPINE G27：准确 beta 衰减率给二次统一 trace depth

二次 cap 上界 m=C*L 与 Rsecondary/Q>L−1，L≥3，给 theta=beta0/(2(C+1))。
实际 trace 的 active-stage 起点因此早于 t−theta/Rsecondary。
本文件只消费已存在的 trace，不从数值比较反推 Good 或空间覆盖。
-/

open Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

/-- C 与 beta0 固定后，二次窗口统一深度独立于 L、Q、Rsecondary。 -/
theorem secondary_depth_lt_uniform_window_CXSP
    {C L Q R β0 : ℝ} (hC : 1 ≤ C) (hL : 3 ≤ L) (hQ : 0 < Q)
    (hR : L - 1 < R / Q) (hβ : 0 < β0) :
    0 < β0 / (2 * (C + 1)) ∧
      (β0 / (2 * (C + 1))) / R < (β0 / (C * L + 1)) / Q := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hL0 : 0 < L := by linarith
  have hCL : 0 < C * L + 1 := by positivity
  have hCp : 0 < C + 1 := by positivity
  have hRp : 0 < R := by
    have hratio : 0 < R / Q := lt_trans (by linarith) hR
    have hh := (lt_div_iff₀ hQ).mp hratio
    simpa only [zero_mul] using hh
  have hb : 0 < β0 / (C * L + 1) := div_pos hβ hCL
  have hratio : β0 / (C + 1) ≤ L * (β0 / (C * L + 1)) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hCp hCL]
    have hden : C * L + 1 ≤ L * (C + 1) := by nlinarith only [hL]
    nlinarith only [mul_le_mul_of_nonneg_left hden hβ.le]
  have hhalf : β0 / (2 * (C + 1)) ≤ (L - 1) * (β0 / (C * L + 1)) := by
    have hmul := mul_le_mul_of_nonneg_right (by linarith : L / 2 ≤ L - 1) hb.le
    have heq : β0 / (2 * (C + 1)) = (β0 / (C + 1)) / 2 := by field_simp
    rw [heq]
    linarith only [hratio, hmul]
  have hstrict := hhalf.trans_lt (mul_lt_mul_of_pos_right hR hb)
  refine ⟨div_pos hβ (by positivity), ?_⟩
  apply (div_lt_iff₀ hRp).mpr
  convert hstrict using 1
  ring

/-- 同一实际 trace 的 first stage 满足统一二次请求；不改变 endpoint 或 carrier。 -/
theorem secondary_trace_start_of_uniform_window_CXSP
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {x : (H.stageAt t).Carrier}
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x)
    {C L Q R β0 : ℝ} (hC : 1 ≤ C) (hL : 3 ≤ L) (hQ : 0 < Q)
    (hR : L - 1 < R / Q) (hβ : 0 < β0)
    (hclock : (a : ℝ) = (t : ℝ) - (β0 / (C * L + 1)) / Q) :
    ∃ first : Fin (H.eventCount + 1),
      H.time first < (t : ℝ) - (β0 / (2 * (C + 1))) / R ∧
      ∃ hfirst : first ≤ H.activeStage t,
        Nonempty (BackwardPointTrace H first (H.activeStage t) hfirst x) := by
  obtain ⟨_hθ, hdepth⟩ := secondary_depth_lt_uniform_window_CXSP hC hL hQ hR hβ
  refine ⟨H.activeStage a, ?_, H.activeStage_mono hat, ⟨B⟩⟩
  have ha := H.activeStage_time_le a
  rw [hclock] at ha
  linarith

end GC.LongTime.Ch11
