import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAge_P6L

/-!
# AD-trunc（合同 rev1 §R3，外审 R-C11-1 §Q9 9.4）：固定深度窗口只遇晚期事件（`_P6L`，可证部分）

P5 给 late records `∀ i, T ≤ eventTime i → GeometricCutoffRecord …`，而 SLT:249 / SLT:249_P6L 要全历史
record family。外审 9.4：对固定归一化深度 `B`，`s_n → ∞`、`s_n Q_n → ∞` ⇒ `s_n − B/Q_n → ∞`，故深度
`B` 窗口最终只遇晚期事件。本文件交付：
* `tendsto_sub_depth_P6L`：`s_n − B/Q_n → ∞`（`s_n Q_n ≥ 2B` 后 `s_n − B/Q_n ≥ s_n/2`）。
* `eventually_window_events_late_P6L`：对任意 `T`，eventually 每个落在深度窗口内的事件时间 `≥ T`，
  故 late records 在窗口事件上全有（以 `records` 前提的形式给出）。
[V] 记录：SLT:249_P6L 的 `records` 只经 BTCC:91_P6L 的 `exists_window_point_of_edist_le` 在事件
`j`（`u ≤ time j.succ`，`u = t − τ`、`τ ≤ θ/Q` 量级）上用 —— 窗口足迹。
**未交（阻塞）**：把 history 截取 / 重置到窗口起点（`time 0 = 0` 要求重新零点化：时间平移、stage 重编号、
`GeometricCutoffRecord` / `IsCanonicalCutoffRecordFamily` / closed slab 的 transport）——树内只有尾端截断
`RetainedCoreHistory.restrict`（截 horizon），没有"丢早期事件"的构造；或者把 `CapWindowPoint` /
`IsCanonicalCutoffRecordFamily` 改写成窗口事件上的部分 family（新 def，需 lead 裁定）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- AD-trunc (1)：`s_n → ∞`、`s_n Q_n → ∞`、`0 < Q_n` ⇒ 固定深度 `B` 的窗口起点 `s_n − B/Q_n → ∞`。 -/
theorem tendsto_sub_depth_P6L {s Q : ℕ → ℝ} {B : ℝ} (hQ : ∀ n, 0 < Q n)
    (hs : Tendsto s atTop atTop) (hsQ : Tendsto (fun n => s n * Q n) atTop atTop) :
    Tendsto (fun n => s n - B / Q n) atTop atTop := by
  have h2 : Tendsto (fun n => (1 / 2 : ℝ) * s n) atTop atTop := hs.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ h2
  filter_upwards [hsQ.eventually_ge_atTop (2 * B)] with n hn
  have hq := hQ n
  have hBQ : B / Q n ≤ s n / 2 := by
    rw [div_le_iff₀ hq, div_mul_eq_mul_div, le_div_iff₀ two_pos]
    linarith
  calc (1 / 2 : ℝ) * s n = s n - s n / 2 := by ring
    _ ≤ s n - B / Q n := sub_le_sub_left hBQ _

/-- AD-trunc (2)：任意 `T`，eventually 深度 `B` 窗口内（`s_n − B/Q_n ≤ τ`）的事件时间 `τ ≥ T`；
于是 P5 late records（`T ≤ τ → record`）在窗口事件上给出 records。 -/
theorem eventually_window_events_late_P6L {s Q : ℕ → ℝ} {B : ℝ}
    (hQ : ∀ n, 0 < Q n) (hs : Tendsto s atTop atTop)
    (hsQ : Tendsto (fun n => s n * Q n) atTop atTop) (T : ℝ) :
    ∀ᶠ n in atTop, ∀ τ : ℝ, s n - B / Q n ≤ τ → T ≤ τ := by
  filter_upwards [(tendsto_sub_depth_P6L hQ hs hsQ).eventually_ge_atTop T] with n hn τ hτ
  exact hn.trans hτ

/-- AD-trunc (2′)，records 形：late family `rec : ∀ τ, T ≤ τ → R τ` 在 eventually 的窗口事件上给出
`R τ`（`R` 任意依赖于事件时间的数据，如 `GeometricCutoffRecord`）。 -/
theorem eventually_window_records_P6L {s Q : ℕ → ℝ} {B T : ℝ}
    (hQ : ∀ n, 0 < Q n) (hs : Tendsto s atTop atTop)
    (hsQ : Tendsto (fun n => s n * Q n) atTop atTop) (R : ℝ → Prop)
    (hrec : ∀ τ, T ≤ τ → R τ) :
    ∀ᶠ n in atTop, ∀ τ : ℝ, s n - B / Q n ≤ τ → R τ :=
  (eventually_window_events_late_P6L hQ hs hsQ T).mono fun _ h τ hτ => hrec τ (h τ hτ)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
