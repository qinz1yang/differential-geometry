import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HsepTwinHSX

/-!
# HSEPX G2：DrvResE 合取 1（K 帧）⇒ E 帧 `hsepT`（`_HSX`，PROVED）

DrvResE_DW（`P6DextDriverDrvW`）∃ 链合取 1：
`∀ T > 0, ∀ C ≥ 0, ∀ᶠ n, ∀ i hi b, σ − T/R < time i.succ →
2·max(3/(1/100)², C·R) < scale(recordsK)`。
沿 `eventPrefix (j n) (tK n)`：records-X := `eventPrefixRecords_C11G2 recordsK`（`static` 定义等，
E 事件 `e` ↦ K 事件 `castLE e`，`time` 定义等）、`ts ≍ σ`、`0 < r`、eventually `1 ≤ R`（取
`C′ := C + 3/r²`）⇒ G1 的 `hsepT` 槽。
* `hsepT_eventPrefix_of_drvSep_HSX`：桥（PROVED）；
* `hsepT_slot_of_drvSep_HSX`：同一结论写成 G1 `drvSlots_K_of_J10_sepT_HSX` 的 `hsepT` 槽逐字
  （`Hs` / `qX` / `T₀X` / `recordsX` 为变量 + 等式前提，`hHsK` 与 DJ 同形），PROVED。
无 `hqR`；无新顶层 binder。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- 数值（`_HSX`）：`0 < r`、`0 ≤ C`、`1 ≤ x` ⇒
`2·max(3/r², C x) ≤ 2·max(3/(1/100)², (C + 3/r²) x)`。 -/
theorem two_max_r_le_HSX {r C x : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hx : 1 ≤ x) :
    2 * max (3 / r ^ 2) (C * x) ≤ 2 * max (3 / ((1 : ℝ) / 100) ^ 2) ((C + 3 / r ^ 2) * x) := by
  have ha : 0 ≤ 3 / r ^ 2 := by positivity
  have h1 : max (3 / r ^ 2) (C * x) ≤ (C + 3 / r ^ 2) * x :=
    max_le (by nlinarith) (by nlinarith)
  have h2 := le_max_right (3 / ((1 : ℝ) / 100) ^ 2) ((C + 3 / r ^ 2) * x)
  linarith

/-- **G2 桥（`_HSX`，PROVED）**：见文件头。 -/
theorem hsepT_eventPrefix_of_drvSep_HSX {r : ℝ} (hr : 0 < r)
    (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (tK : ℕ → ℝ)
    (hjt : ∀ n, (K n).time (j n).castSucc < tK n) (htj : ∀ n, tK n < (K n).time (j n).succ)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (R : ℕ → ℝ) (hR1 : ∀ᶠ n in atTop, 1 ≤ R n)
    (ts : ∀ n, Icc (0 : ℝ) ((K n).eventPrefix (j n) (tK n) (hjt n) (htj n)).toHistory.horizon)
    (hσ : ∀ n, (ts n : ℝ) = σ n)
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n))
    (hsepK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
          ((recordsK n i hi).static b).neck.scale) :
    ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (e : Fin ((K n).eventPrefix (j n) (tK n) (hjt n) (htj n)).toHistory.eventCount)
        (he : T₀K n ≤ ((K n).eventPrefix (j n) (tK n) (hjt n) (htj n)).toHistory.time e.succ) b,
        (ts n : ℝ) - T / R n <
          ((K n).eventPrefix (j n) (tK n) (hjt n) (htj n)).toHistory.time e.succ →
        2 * max (3 / r ^ 2) (C * R n) <
          (((K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n) e he).static
            b).neck.scale := by
  intro T hT C hC
  filter_upwards [hsepK T hT (C + 3 / r ^ 2) (by positivity), hR1] with n hn hRn
  intro e he b hlt
  have hlt' : (σ n : ℝ) - T / R n <
      (K n).time (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) e).succ := by
    rw [← hσ n]
    exact hlt
  exact (two_max_r_le_HSX hr hC hRn).trans_lt
    (hn (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) e) he b hlt')

/-- **G2 槽形（`_HSX`，PROVED）**：G1 `drvSlots_K_of_J10_sepT_HSX` 的 `hsepT` 槽逐字（E 帧变量
`Hs ts qX T₀X recordsX`），由 DrvResE 合取 1 + `hHsK`（DJ 同形）+ records-X 取 recordsK 的
eventPrefix 限制付。 -/
theorem hsepT_slot_of_drvSep_HSX {r : ℝ} (hr : 0 < r)
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (R : ℕ → ℝ)
    (hR1 : ∀ᶠ n in atTop, 1 ≤ R n)
    (qX : ℕ → CutoffParameters) (T₀X : ℕ → ℝ)
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (qX n))
    (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (tK : ℕ → ℝ)
    (hjt : ∀ n, (K n).time (j n).castSucc < tK n) (htj : ∀ n, tK n < (K n).time (j n).succ)
    (hHsK : ∀ n, Hs n = ((K n).eventPrefix (j n) (tK n) (hjt n) (htj n)).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (hσ : ∀ n, (ts n : ℝ) = σ n)
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n))
    (hq : qX = qK) (hT₀ : T₀X = T₀K)
    (hrec : HEq recordsX
      (fun n => (K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n)))
    (hsepK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
          ((recordsK n i hi).static b).neck.scale) :
    ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, (ts n : ℝ) - T / R n < (Hs n).time e.succ →
        2 * max (3 / r ^ 2) (C * R n) < ((recordsX n e he).static b).neck.scale := by
  have hHs : Hs = fun n => ((K n).eventPrefix (j n) (tK n) (hjt n) (htj n)).toHistory :=
    funext hHsK
  subst hHs hq hT₀
  obtain rfl := eq_of_heq hrec
  exact hsepT_eventPrefix_of_drvSep_HSX hr K j tK hjt htj σ R hR1 ts hσ recordsK hsepK

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
