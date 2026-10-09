import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointProtectionC11G
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Pre841DefsC11K

/-!
# P6 几何输入 G3：late records 供给（O-CH11-P6GEO，后缀 `_C11G`）

DIST `hevent_of_records_C11D` / `hrate_of_endpoint_bounds_C11D` 的 records 侧前提（P6N 约定的 late records
`records n e : T₀ ≤ time e⁺ → GeometricCutoffRecord`、`hOld`、`hcan`、`hacc ≤ 1/2`、
`hDm : transitionEnd + 10 < modelRadius`、`hT₀ : T₀ ≤ s_n − T/R_n` eventually）加上 G1 的参数前提
（精度 `≤ ε₀`、阶 `≥ 2`）与 scale 分离。

* **P5 路**（enhanced profile 的 `P5Linked_C11E` = `LateLinkedRecordsSupply_C11E`）
  `exists_lateRecords_of_P5Linked_C11G`：取 `D = transitionEnd + 11`、`ζ = min(1/2, ε₀)`、`m = 2`
  ⇒ 一个**常数** `T₀` 与逐 `n` 的参数 `q n`、late records、canonical windows（linked ⇒ canonical）、
  全部参数前提；`hOld` = record 字段 `old_eq_retained`。
* **Pre841 路** `lateRecords_of_pre841_C11G`：native `records` 是**全** records（任意 `T₀`）、
  `canonical_windows`；但参数 `N.params` 的精度 / 阶 / 半径**不在** native 字段里——`hacc`、`≤ ε₀`、
  `2 ≤ modelOrder`、`transitionEnd + 10 < modelRadius` 须显式（列于 state）。native `pinching` 直接是 G2 的
  `hpin`（`a₀ = pinchingShift`）。
* 时间与 scale：`hT₀_of_late_C11G`、`hlate_of_late_C11G`（`s_n → ∞`、`R_n ≥ 1`）、
  `tendsto_s_of_seed_C11G`（`t_n → ∞`、`2r_n² < t_n`、`aSeed = t − r² ≤ s` ⇒ `s_n → ∞`）、
  `hscale_of_neckRadius_C11G`（G1 单 record scale 下界 ⇒ G1 的 `2M < scale`，条件
  `Λ δ(time e⁺) ≤ 1/2`、`4 M ρ(time e⁺)² ≤ 1`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Topology

namespace GC.LongTime.Ch11

universe u

/-- **P5Linked ⇒ late records（`_C11G`）**：`LateLinkedRecordsSupply_C11E F q₀`、`ε₀ > 0` ⇒ 常数 `T₀`、
参数 `q n`（`δ / ρ / Λ` 与 `q₀` 相同）、late records（`T₀ ≤ time e⁺`）、canonical windows，且
`modelAccuracy ≤ min(1/2, ε₀)`、`2 ≤ modelOrder`、`transitionEnd + 10 < modelRadius`。 -/
theorem exists_lateRecords_of_P5Linked_C11G {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q₀ : CutoffParameters}
    (hP5 : LateLinkedRecordsSupply_C11E F q₀) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ (T₀ : ℝ) (q : ℕ → CutoffParameters)
      (records : ∀ n (e : Fin (F.tower.history n).eventCount),
        T₀ ≤ (F.tower.history n).time e.succ →
        GeometricCutoffRecord (F.tower.history n).toHistory e (q n)),
      (∀ n e (he : T₀ ≤ (F.tower.history n).time e.succ) b,
        ((records n e he).static b).hasCanonicalWindow) ∧
      (∀ n, (q n).modelAccuracy ≤ 1 / 2) ∧ (∀ n, (q n).modelAccuracy ≤ ε₀) ∧
      (∀ n, 2 ≤ (q n).modelOrder) ∧
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) ∧
      ∀ n, (q n).delta = q₀.delta ∧ (q n).neckRadius = q₀.neckRadius ∧
        (q n).recenterConstant = q₀.recenterConstant := by
  obtain ⟨T, hT⟩ := hP5 (StandardCap.transitionEnd + 11) (min (1 / 2) ε₀) 2
    (lt_min (by norm_num) hε₀)
  choose q hq using hT
  choose records hrec using fun n => (hq n).2.2.2.2.2.2.2
  refine ⟨T, q, records, fun n e he b => linkedCanonicalWindow_hasCanonicalWindow_C11E _
    (hrec n e he b), fun n => (hq n).2.2.2.2.2.1.trans (min_le_left _ _),
    fun n => (hq n).2.2.2.2.2.1.trans (min_le_right _ _), fun n => (hq n).2.2.2.2.2.2.1,
    fun n => ?_, fun n => ⟨(hq n).1, (hq n).2.1, (hq n).2.2.2.1⟩⟩
  linarith [(hq n).2.2.2.2.1]

/-- **Pre841 ⇒ late records（`_C11G`）**：native 的全 records 当作任意 `T₀` 的 late records；
canonical windows 与 `old = retainedCore` 由 native / record 字段给。 -/
theorem lateRecords_of_pre841_C11G {Hs : ℕ → ObservedHistory.{u}}
    (N : Pre841NativeData_C11K Hs) (T₀ : ℕ → ℝ) :
    ∃ records : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
        GeometricCutoffRecord (Hs n) e N.params,
      (∀ n e (he : T₀ n ≤ (Hs n).time e.succ) b,
        ((records n e he).static b).hasCanonicalWindow) ∧
      ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
        ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore :=
  ⟨fun n e _ => N.records n e, fun n e _ b => N.canonical_windows n e b,
    fun n e _ => (N.records n e).old_eq_retained⟩

/-! ## 时间与 scale -/

/-- **`hT₀`（`_C11G`）**：常数 `T₀`、`s_n → ∞`、eventually `R_n ≥ 1` ⇒ `∀ T > 0`，eventually
`T₀ ≤ s_n − T/R_n`。 -/
theorem hT₀_of_late_C11G {Hs : ℕ → ObservedHistory.{u}} (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (R : ℕ → ℝ) (T₀ : ℝ) (hs : Tendsto (fun n => (s n : ℝ)) atTop atTop)
    (hR1 : ∀ᶠ n in atTop, 1 ≤ R n) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ ≤ (s n : ℝ) - T / R n := by
  intro T hT
  filter_upwards [hs.eventually_ge_atTop (T₀ + T), hR1] with n h1 h2
  have h3 : T / R n ≤ T := div_le_self hT.le h2
  linarith

/-- **`hlate`（G2，`_C11G`）**：`s_n → ∞`、eventually `R_n ≥ 1` ⇒ `∀ T > 0`，eventually
`1 ≤ R_n (s_n − T/R_n)`。 -/
theorem hlate_of_late_C11G {Hs : ℕ → ObservedHistory.{u}} (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (R : ℕ → ℝ) (hs : Tendsto (fun n => (s n : ℝ)) atTop atTop)
    (hR1 : ∀ᶠ n in atTop, 1 ≤ R n) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n) := by
  intro T hT
  filter_upwards [hs.eventually_ge_atTop (1 + T), hR1] with n h1 h2
  have hR0 : 0 < R n := by linarith
  have h3 : R n * (T / R n) = T := by field_simp
  rw [mul_sub, h3]
  nlinarith

/-- **`s_n → ∞`（`_C11G`）**：种子时刻 `t_n → ∞`、`2 r_n² < t_n`、`aSeed_n = t_n − r_n² ≤ s_n`
⇒ `s_n ≥ t_n/2 → ∞`。 -/
theorem tendsto_s_of_seed_C11G {Hs : ℕ → ObservedHistory.{u}}
    (t s aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop) (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) (has : ∀ n, aSeed n ≤ s n) :
    Tendsto (fun n => (s n : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) (hlate.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have h1 : (aSeed n : ℝ) ≤ s n := has n
  have h2 := htime n
  have h3 := hclock n
  linarith

/-- **G1 的 scale 分离 ⇐ 中立 neck 半径（`_C11G`）**：late records 的 `Λ δ(time e⁺) ≤ 1/2`、
`4 M ρ(time e⁺)² ≤ 1` ⇒ 每个 static cap `2M < scale`（G1 单 record 下界
`(2ρ²)⁻¹ < scale`）。 -/
theorem hscale_of_neckRadius_C11G {H : ObservedHistory.{u}} {q : CutoffParameters} {T₀ M : ℝ}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (hΛδ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      q.recenterConstant * q.delta (H.time e.succ) ≤ 1 / 2)
    (hρ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      4 * M * q.neckRadius (H.time e.succ) ^ 2 ≤ 1) :
    ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      2 * M < ((records e he).static b).neck.scale := by
  intro e he b
  have h := (records e he).inv_two_mul_sq_lt_static_scale_C11G (hΛδ e he) b
  have hρpos := q.neckRadius_pos _ (H.time_nonneg e.succ)
  have h2 : 2 * M ≤ (2 * q.neckRadius (H.time e.succ) ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]
    linarith [hρ e he]
  linarith

/-- **consumer（G3）**：P5Linked（沿子列 `ind`）⇒ DIST 序列层 records 侧的全部前提
（`records`、`hOld`、`hcan`、`hacc`、`hDm`、`hT₀`）+ G1 的精度 `≤ ε₀` / 阶 `≥ 2`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q₀ : CutoffParameters} (hP5 : LateLinkedRecordsSupply_C11E F q₀) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (ind : ℕ → ℕ) (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (R : ℕ → ℝ) (hs : Tendsto (fun n => (s n : ℝ)) atTop atTop)
    (hR1 : ∀ᶠ n in atTop, 1 ≤ R n) :
    ∃ (T₀ : ℕ → ℝ) (q : ℕ → CutoffParameters)
      (records : ∀ n (e : Fin (F.tower.history (ind n)).toHistory.eventCount),
        T₀ n ≤ (F.tower.history (ind n)).toHistory.time e.succ →
        GeometricCutoffRecord (F.tower.history (ind n)).toHistory e (q n)),
      (∀ n (e : Fin (F.tower.history (ind n)).toHistory.eventCount),
        T₀ n ≤ (F.tower.history (ind n)).toHistory.time e.succ →
        ((F.tower.history (ind n)).toHistory.event e).old =
          ((F.tower.history (ind n)).toHistory.event e).transition.trace.retainedCore) ∧
      (∀ n e (he : T₀ n ≤ (F.tower.history (ind n)).toHistory.time e.succ) b,
        ((records n e he).static b).hasCanonicalWindow) ∧
      (∀ n, (q n).modelAccuracy ≤ 1 / 2) ∧ (∀ n, (q n).modelAccuracy ≤ ε₀) ∧
      (∀ n, 2 ≤ (q n).modelOrder) ∧
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) ∧
      ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (s n : ℝ) - T / R n := by
  obtain ⟨T₀, q, records, hcan, hacc, hacc0, hm, hDm, -⟩ :=
    exists_lateRecords_of_P5Linked_C11G hP5 hε₀
  exact ⟨fun _ => T₀, fun n => q (ind n), fun n e he => records (ind n) e he,
    fun n e he => (records (ind n) e he).old_eq_retained, fun n e he b => hcan (ind n) e he b,
    fun n => hacc (ind n), fun n => hacc0 (ind n), fun n => hm (ind n), fun n => hDm (ind n),
    hT₀_of_late_C11G s R T₀ hs hR1⟩

end GC.LongTime.Ch11
