import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeObject_P6N

set_option autoImplicit false

/-!
# CX-SPINE G9：KWIRE v5 种子资格的精确 transport

cutoff 参数使用实际 rescale_P6N：时间除以 c，半径除以 √c。
整个闭窗口上的 neckRadius 上界双向等价；特别地，seed half-window 的资格不因归一化改变。
antitone 半径把该资格化为左端点检验。此处不生产未给定的 seed eligibility。
-/

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters

/-- 实际 cutoff 参数在整个闭 time-window 上的半径上界随重标度双向搬运。 -/
theorem neckRadius_window_rescale_iff_CXSP {q : CutoffParameters}
    {c : ℝ} (hc : 0 < c) {a b r : ℝ} :
    (∀ w : ℝ, a / c ≤ w → w ≤ b / c →
      (q.rescale_P6N c hc).neckRadius w ≤ r / Real.sqrt c) ↔
    (∀ s : ℝ, a ≤ s → s ≤ b → q.neckRadius s ≤ r) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  constructor
  · intro h s has hsb
    have hbound := h (s / c) ((div_le_div_iff_of_pos_right hc).mpr has)
      ((div_le_div_iff_of_pos_right hc).mpr hsb)
    rw [(q.rescale_P6N_eval c hc s).2.1] at hbound
    exact (div_le_div_iff_of_pos_right hs).mp hbound
  · intro h w haw hwb
    have haw' : a ≤ c * w := by
      simpa only [mul_comm] using (div_le_iff₀ hc).mp haw
    have hwb' : c * w ≤ b := by
      simpa only [mul_comm] using (le_div_iff₀ hc).mp hwb
    exact (div_le_div_iff_of_pos_right hs).mpr (h (c * w) haw' hwb')

/-- KWIRE v5 的整个 seed half-window guard 与重标度后的 guard 严格等价。 -/
theorem seedScale_half_window_rescale_iff_CXSP {q : CutoffParameters}
    {c : ℝ} (hc : 0 < c) {t r : ℝ} :
    (∀ w : ℝ, t / c - (r / Real.sqrt c) ^ 2 / 2 ≤ w → w ≤ t / c →
      (q.rescale_P6N c hc).neckRadius w ≤ r / Real.sqrt c) ↔
    (∀ s : ℝ, t - r ^ 2 / 2 ≤ s → s ≤ t → q.neckRadius s ≤ r) := by
  have hleft : t / c - (r / Real.sqrt c) ^ 2 / 2 = (t - r ^ 2 / 2) / c := by
    rw [div_pow, Real.sq_sqrt hc.le]
    ring
  rw [hleft]
  exact neckRadius_window_rescale_iff_CXSP hc

/-- antitone cutoff 半径的 seed half-window 资格恰为左端点的尺度上界。 -/
theorem seedScale_half_window_iff_left_CXSP {q : CutoffParameters}
    (hanti : AntitoneOn q.neckRadius (Ici 0)) {t r : ℝ}
    (hleft : 0 ≤ t - r ^ 2 / 2) :
    (∀ s : ℝ, t - r ^ 2 / 2 ≤ s → s ≤ t → q.neckRadius s ≤ r) ↔
    q.neckRadius (t - r ^ 2 / 2) ≤ r := by
  constructor
  · intro h
    exact h _ le_rfl (by nlinarith [sq_nonneg r])
  · intro h s hlow _hup
    exact (hanti hleft (hleft.trans hlow) hlow).trans h

/-- consumer：实际左端点资格可直接送入归一化后的 v5 seed guard。 -/
example {q : CutoffParameters} {c t r : ℝ} (hc : 0 < c)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hleft : 0 ≤ t - r ^ 2 / 2)
    (hseed : q.neckRadius (t - r ^ 2 / 2) ≤ r) :
    ∀ w : ℝ, t / c - (r / Real.sqrt c) ^ 2 / 2 ≤ w → w ≤ t / c →
      (q.rescale_P6N c hc).neckRadius w ≤ r / Real.sqrt c := by
  exact (seedScale_half_window_rescale_iff_CXSP hc).mpr
    ((seedScale_half_window_iff_left_CXSP hanti hleft).mpr hseed)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutoffParameters
