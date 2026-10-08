import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedRecordScaleCXSP

set_option autoImplicit false

/-!
# native 有界 ratio 子情形的 record-scale 分离（O-CH11-SPINE-B G4a，后缀 `_C11SP`）

guard 链里 `q.neckRadius t ≤ r` 的**唯一真实消费点**是 G21 `exists_late_seed_record_scale_CXSP`
（`P6PreparedTime{FirstExit:128–138, Survival:151–156}CXSP` 经 `crossed_event_mem_half_window_CXSP`
调用）：它给"窗内每个 crossed event 的 static cap 满足 `4M < neck.scale`"，下游两处花它：
(a) birth 排除（G19 protection：trace 点不在 cap 内窗）；(b) (D4) no-shortcut 的端点保护
（`surgery_no_shortcut_C11D`、CXJD `hprotC_of_ceiling_CXJD`）。

**本页（PROVED）**：G21 里的 `r` 只是一个正数，与 seed 半径无关；把 `L` 换成 `Λ²·L` 即得
**`nr(t) ≤ Λ·r` 版**的同一分离。所以 native 的有界 ratio 子情形（`ρ < nr(τ) ≤ Λ ρ`）的 (a)(b) 两处
与 guard 完全同理——只需把 guard 链从 G21 起的各叶把 `nr ≤ r` 换成 `nr ≤ Λ r`（`Λ` 在 `T₀` 之前），
是机械的参数穿线。**真缺口只剩 `ρ/nr(τ) → 0` 子情形**（见 `native-route.md` §G4）。
-/

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology

namespace GC.LongTime.Ch11

universe u

/-- **G4a（PROVED）**：`nr(t) ≤ Λ·r` 版 record-scale 分离；阈值 `T₀` 先于全部 queries。 -/
theorem exists_late_seed_record_scale_of_ratio_C11SP
    (histories : ℕ → ObservedHistory.{u}) (params : CutoffParameters)
    (records : ∀ n, ∀ e : Fin (histories n).eventCount,
      GeometricCutoffRecord (histories n) e params)
    (hdecay : Tendsto params.delta atTop (𝓝 0))
    (hrecent : ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (histories n).eventCount,
        (histories n).time e.succ ∈ Icc (t / 2) t →
        ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t)
    (L Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (t : ℝ), T₀ ≤ t → ∀ n : ℕ, ∀ e : Fin (histories n).eventCount,
        (histories n).time e.succ ∈ Icc (t / 2) t →
        ∀ (r M : ℝ), 0 < r → params.neckRadius t ≤ Λ * r → M * r ^ 2 ≤ L →
        ∀ b, 4 * M < ((records n e).static b).neck.scale := by
  obtain ⟨T₀, hT₀, hsep⟩ :=
    exists_late_seed_record_scale_CXSP histories params records hdecay hrecent (Λ ^ 2 * L)
  refine ⟨T₀, hT₀, fun t ht n e he r M hr hnr hML b => ?_⟩
  have hML' : M * (Λ * r) ^ 2 ≤ Λ ^ 2 * L := by
    have h : M * (Λ * r) ^ 2 = Λ ^ 2 * (M * r ^ 2) := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_left hML (sq_nonneg Λ)
  exact hsep t ht n e he (Λ * r) M (mul_pos hΛ hr) hnr hML' b

end GC.LongTime.Ch11
