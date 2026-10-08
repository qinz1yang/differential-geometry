import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcenProducerP6HE
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateKdataNomDiagCXKN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeRecord_P6M

/-!
# 五合取 late-records binder `hrec6` 的 producer（S-CH11-HREC6 G1/G2，后缀 `_P6H6`）

HCENP 遗留：`hcenE_of_noShortcut_P6HE` 的 binder `hrec6`（= `hcapWL_of_records_P6HB` 的 `hrec` 加第 5
合取项 `∀ b, 6 < (Rc.static b).neck.scale`）。本文件从 KNOM 联合 witness
（`exists_lateKdata_nominal_diag_CXKN`，NOMID 固定档）经 Ho→K 的 `GeometricCutoffRecord.rescale_P6M`
接线产出 `hrec6` **逐字**（脚本核对：结论 = `P6HcenProducerP6HE` 的 `hrec6` binder，字节相同）。

* **`hjoint_of_knom_P6H6`（G1a，KNOM 实例化）**：`hP5L`（nominal 形 supply，同 CXKN）+ `hδq` + `hρa` ⇒
  `∃ Tmin : (ℕ → ℝ) → ℕ → ℝ`，对任一 `T₀ ≥ Tmin` 与任意 `ind c`（`c k > 0`），同一 `recordsK`
  给出：canonical window ∧ `accuracy ≤ 1/(n+1)` ∧ `n+1 ≤ radius` ∧ `n+2 ≤ order` ∧ **hOpen 第三条形**
  `(n+1)·max((n+1)/c n)(Q n) ≤ scale`（Ho 单位；KNOM 的 `S n ≤ scale` 合取项，`S n := max 1 (…)`）。
  `Tmin` 依赖 `c`（因 `S` 含 `(n+1)/c n`），不依赖 `ind`（KNOM 的量词序）。
* **`hrec6_of_nomDiag_P6H6`（G1b，主定理）**：`hjoint`（G1a 的结论形）+ `hlateT` ⇒ `hrec6` 逐字。
  records 用 `rescale_P6M`（`pp := (p k).rescale_P6N (c k)`，`scale ↦ c k · scale`，
  `rescale_P6M_scale`）；`6 < c k · scale` 用 HCENP 小引理 `six_lt_rescaled_scale_P6HE`（`k ≥ 2`）；
  `accuracy / radius / order` 的 `rfl` 重标度 + NOMID 固定档的 eventual 比较。
* **`hrec6_of_knom_P6H6`（G1c）**：G1a ∘ G1b 的闭合形。
* **`hrec6_of_P5L_compat_P6H6`（G1d，另一条 producer）**：固定档 P5L supply + `hδq` + `hρa` +
  PROVISIONAL `hcompat`（事件层 `q.delta (time) ≤ 1/(2·max 1 (3/c k)·ρ(0))`）⇒ `hrec6` 逐字；
  `6 < scale` 经 `inv_two_mul_sq_lt_static_scale_record_delta_P6M3`（`2 S² < scale_Ho`）
  + `rescale_P6M_scale`。
  没有 KNOM 对角档的 `(n+1)` 因子，`hcompat` 在 `c` 有下界时可满足（见下）。
* **`hcapWL_of_hrec6_P6H6`（G2a）**：`hrec6` ⇒ `hrec`（`hrec_of_hrec6_P6HE`）⇒
  `hcapWL_of_records_P6HB` 的 `hcapWL` 槽；文件中的 `example` 把 G1c 喂给它。G2b：`example` 喂
  `hcenE_of_noShortcut_P6HE` 的 `hrec6` 槽。
* **`hrec_of_P5L_P6H6` / `hcapWL_of_P5L_P6H6`（G2c，无条件）**：固定档 P5L supply
  `LateLinkedRecordsSupply_C11E F q` ⇒ 4 合取 `hrec` ⇒ `hcapWL` 槽，**不需要** lateness / hOpen / KNOM
  对角档（`hrec` 的精度 / 半径 / 阶是固定目标，阈值 `T` 与 `k` 无关）。即 `hcapWL` 槽已可完全付掉；
  只有第 5 合取项 `6 < scale` 才需要 `hlateT`。

**PROVISIONAL binder（唯一的新前提）`hlateT`**：lateness——events 的 Ho 时间 `≥ T₀ c k`（KNOM 阈值
`Tmin c k` 以上）。`hrec6` 的冻结形只带 `Tendsto (c k · Kh.time) atTop atTop`，不带 `T₀ k ≤ c k · aSeed k`，
所以 KNOM 的 late 阈值必须由调用方（顶层 `hcenE` 接线：`time (i k).succ ≥ (k+1)/2`，见
`hcenE_of_noShortcut_P6HE` 里 `hlate` 的推导）通过 `T₀` 的选取付掉。owner = hOpen 第三条
（P6WR `hOpen`，R-C11-7）所在的顶层接线车道。注意：`hrec6` 的 `6 < scale` 对**任意** `c` 不成立
（`scale_K = c · scale_Ho`，`c` 极小时 `scale_Ho ≈ 1/δ²` 不够），所以 `hlateT` 必须按 `c` 取阈值
（`T₀ c`）——这正是 hOpen 第三条 `(n+1)/c n` 的来源。
**G1b 的 `hlateT` 对"任意 `i`"一般不可满足**（诚实说明）：对角档 `S n ~ (n+1)²/c n` 使 KNOM 的
late 阈值 `Tmin c n` 一般随 `n` 增长（KNOM 不给 `Tmin` 的界），而 `hrec6` 的 `i` 只被
`Tendsto (c k · Kh.time)` 约束，event 时间可任意慢地 `→ ∞`；因此 `hlateT` 成立当且仅当 events 的
时间增长快于 `T₀ c k`。`hrec6` 实际只需 `6 < c k · scale_Ho`（`S ≈ 3/c k`，无 `(n+1)`
因子），G1d 的 `hcompat` 就是这个最弱的、事件层可检查的相容条件。repair target（供 lead 裁定，不在本
车道改形）：要么让顶层接线提供 `hcompat`（`q.delta` 在 event 时间的衰减 ≥ `c k` 的阶），要么把
`hrec6` / `hcenE` 的 `hlate` 前提加强为 `∀ k, (k+1)/2 ≤ c k · Kh.time (i k).succ`
（`hcenE_of_noShortcut_P6HE` 内部已推出该不等式）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

/-! ## 1. G1a：KNOM 联合 witness 的实例化（NOMID 固定档 + hOpen 第三条形） -/

/-- **KNOM 实例化（G1a，`_P6H6`）**：`exists_lateKdata_nominal_diag_CXKN` 取 NOMID 固定档
（`Rn n = n+1`、`ζ n = δ₀ n = 1/(n+1)`、`m₀ n = n+2`）与 `S n := max 1 ((n+1)·max((n+1)/c n)(Q n))`
（`c` 是外部重标度序列；`Tmin` 依赖 `c`、不依赖 `ind`）。同一 `recordsK` 给出 canonical window、
三个模型数据下界与 **hOpen 第三条形** `(n+1)·max((n+1)/c n)(Q n) ≤ scale`。 -/
theorem hjoint_of_knom_P6H6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (recs : ∀ k (i : Fin (F.tower.history k).eventCount),
      GeometricCutoffRecord (F.tower.history k).toHistory i q) (Q : ℕ → ℝ)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (F.tower.history k).eventCount,
        T ≤ (F.tower.history k).time i.succ →
        GeometricCutoffRecord (F.tower.history k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) ∧
      ∀ i hi, (records i hi).nominalRadius = (recs k i).nominalRadius ∧
        (records i hi).delta = (recs k i).delta ∧
        (records i hi).order = (recs k i).order ∧
        (∀ α, HEq ((records i hi).neck α) ((recs k i).neck α)) ∧
        (∀ b, ((records i hi).static b).neck.scale = ((recs k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records i hi).static b).inclusion (((records i hi).static b).witness.cap z) =
            ((recs k i).static b).inclusion (((recs k i).static b).witness.cap z))
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) :
    ∃ Tmin : (ℕ → ℝ) → ℕ → ℝ, ∀ T₀ : (ℕ → ℝ) → ℕ → ℝ, (∀ c n, Tmin c n ≤ T₀ c n) →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ), (∀ k, 0 < c k) →
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ c n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
        (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
        (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧ (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
        (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤
          ((recordsK n i hi).static b).neck.scale) := by
  have key : ∀ c : ℕ → ℝ, ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) →
      ∀ ind : ℕ → ℕ, ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
        (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
        (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧ (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
        (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤
          ((recordsK n i hi).static b).neck.scale) := by
    intro c
    obtain ⟨Tmin, hT⟩ := exists_lateKdata_nominal_diag_CXKN recs
      (fun n => max 1 (((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n)))
      (fun n => (n : ℝ) + 1) (fun n => 1 / ((n : ℝ) + 1)) (fun n => 1 / ((n : ℝ) + 1))
      (fun n => n + 2) (fun n => le_max_left _ _) (fun n => by positivity)
      (fun n => by positivity) hP5L hδq hρa
    refine ⟨Tmin, fun T₀ hT₀ ind => ?_⟩
    obtain ⟨p, recordsK, hcan, hacc, hrad, hord, hsc, -⟩ := hT T₀ hT₀ ind
    exact ⟨p, recordsK, hcan, hacc, hrad, hord,
      fun n i hi b => (le_max_right _ _).trans (hsc n i hi b)⟩
  choose Tmin hT using key
  exact ⟨Tmin, fun T₀ hT₀ ind c _ => hT c (T₀ c) (hT₀ c) ind⟩

/-! ## 2. G1b：`hrec6` 逐字（Ho→K 的 `rescale_P6M` 接线） -/

/-- **`hrec6` producer（G1b 主定理，`_P6H6`）**：结论 = `hcenE_of_noShortcut_P6HE` 的 binder `hrec6`
**逐字**（`verify.py` 字节核对）。输入 `hjoint`（G1a 结论形：KNOM 联合 witness + hOpen 第三条形的
scale 下界，Ho 单位）与 **PROVISIONAL** `hlateT`（lateness：event 的 Ho 时间 `≥ T₀ c k`，见文件头）。
K 层 record = `rescale_P6M` 的像：`pp := (p k).rescale_P6N (c k)`，`scale ↦ c k · scale`。 -/
theorem hrec6_of_nomDiag_P6H6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (Q : ℕ → ℝ) (T₀ : (ℕ → ℝ) → ℕ → ℝ)
    (hjoint : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ), (∀ k, 0 < c k) →
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ c n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
        (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
        (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧ (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
        (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤
          ((recordsK n i hi).static b).neck.scale))
    (hlateT : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, T₀ c k ≤ (F.tower.history (ind k)).time (i k).succ) :
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale := by
  intro ind c hc Kh i hlate εcap Rcap mcap hεcap
  obtain ⟨p, recordsK, hcan, hacc, hrad, hord, hsc⟩ := hjoint ind c hc
  have hT := hlateT ind c hc i hlate
  have h1 : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) ≤ εcap :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hεcap)).mono
      fun _ h => h.le
  have h2 : ∀ᶠ k : ℕ in atTop, Rcap ≤ (k : ℝ) + 1 :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).eventually_ge_atTop Rcap
  have h3 : ∀ᶠ k : ℕ in atTop, mcap ≤ k + 2 :=
    (eventually_ge_atTop mcap).mono fun k hk => hk.trans (Nat.le_add_right k 2)
  filter_upwards [hT, h1, h2, h3, eventually_ge_atTop 2] with k hk hk1 hk2 hk3 hk4
  refine ⟨(p k).rescale_P6N (c k) (hc k), (recordsK k (i k) hk).rescale_P6M (c k) (hc k),
    fun b => ?_, (hacc k).trans hk1, hk2.trans (hrad k), hk3.trans (hord k), fun b => ?_⟩
  · exact ((recordsK k (i k) hk).static b).hasCanonicalWindow_rescale_P6M (hcan k (i k) hk b)
      (c k) (hc k)
  · have e : (((recordsK k (i k) hk).rescale_P6M (c k) (hc k)).static b).neck.scale =
        c k * ((recordsK k (i k) hk).static b).neck.scale :=
      ((recordsK k (i k) hk).static b).rescale_P6M_scale (c k) (hc k)
    exact lt_of_lt_of_eq (six_lt_rescaled_scale_P6HE hk4 (hc k) (hsc k (i k) hk b)) e.symm

/-- 算术：`2 S² < s`，`S = max 1 (3/c)` ⇒ `6 < c · s`（`c S ≥ 3`、`S ≥ 1`）。 -/
theorem six_lt_rescaled_of_sq_P6H6 {c s : ℝ} (hc : 0 < c)
    (h : 2 * (max 1 (3 / c)) ^ 2 < s) : 6 < c * s := by
  have hS1 : (1 : ℝ) ≤ max 1 (3 / c) := le_max_left _ _
  have hS2 : 3 / c ≤ max 1 (3 / c) := le_max_right _ _
  have hcS : 3 ≤ c * max 1 (3 / c) := by
    have := (div_le_iff₀ hc).mp hS2
    linarith [mul_comm c (max 1 (3 / c))]
  have h1 : 3 ≤ c * (max 1 (3 / c)) ^ 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left h hc]

/-- **`hrec6` 的另一条 producer（G1d，`_P6H6`，不经 KNOM 的 `Tmin`）**：固定档 P5L supply
`LateLinkedRecordsSupply_C11E F q`（精度 / 半径 / 阶是固定目标，阈值与 `k` 无关）+ `hδq` + `hρa`
+ **PROVISIONAL `hcompat`**（`c` 与 event 时间的相容性，Ho 单位）：
`q.delta (time (i k).succ) ≤ 1 / (2 · max 1 (3/c k) · q.neckRadius 0)`。每个 record 由
`inv_two_mul_sq_lt_static_scale_record_delta_P6M3`（`ρ₀ := 1/(2S)`、`S := max 1 (3/c k)`）得
`2 S² < scale_Ho`，故 `6 < c k · scale_Ho = scale_K`（`rescale_P6M_scale`）。与 G1b 的区别：
`hcompat` 是**事件层可检查的**解析条件（`δ` 的衰减对 `c k`），**没有** KNOM 对角档的
`(n+1)` 因子，故不要求 lateness 阈值随 `k` 增长（G1b 的 `hlateT` 在对角档下对任意 `i` 不可满足，
见文件头）。结论 = `hrec6` 逐字。 -/
theorem hrec6_of_P5L_compat_P6H6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0))
    (hcompat : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, q.delta ((F.tower.history (ind k)).time (i k).succ) ≤
          1 / (2 * max 1 (3 / c k) * q.neckRadius 0)) :
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale := by
  intro ind c hc Kh i hlate εcap Rcap mcap hεcap
  obtain ⟨T, hT⟩ := hP5L Rcap εcap mcap hεcap
  have hΛ : 0 < q.recenterConstant := by linarith [q.recenterConstant_ge_four]
  obtain ⟨Tδ, hTδ⟩ := Filter.eventually_atTop.mp
    (hδq.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * q.recenterConstant))))
  have hev : ∀ᶠ k in atTop, max T Tδ ≤ (F.tower.history (ind k)).time (i k).succ := by
    filter_upwards [hlate.eventually_ge_atTop (max T Tδ)] with k hk
    have e : c k * (Kh k).time (i k).succ = (F.tower.history (ind k)).time (i k).succ :=
      mul_div_cancel₀ _ (hc k).ne'
    exact e ▸ hk
  filter_upwards [hev, hcompat ind c hc i hlate] with k hk hkc
  obtain ⟨p, hpδ, hpρ, -, hprc, hD, hacc, hord, records, hlink⟩ := hT (ind k)
  have hkT : T ≤ (F.tower.history (ind k)).time (i k).succ := (le_max_left _ _).trans hk
  have hkδ : q.delta ((F.tower.history (ind k)).time (i k).succ) ≤
      1 / (2 * q.recenterConstant) := hTδ _ ((le_max_right _ _).trans hk)
  have ht0 : 0 ≤ (F.tower.history (ind k)).time (i k).succ :=
    (F.tower.history (ind k)).toHistory.time_nonneg (i k).succ
  have hdel1 := q.delta_lt_one _ ht0
  have hdel0 := q.delta_pos _ ht0
  have hρ₁ : 0 < q.neckRadius 0 := q.neckRadius_pos 0 le_rfl
  have hSpos : 0 < max 1 (3 / c k) := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨p.rescale_P6N (c k) (hc k), (records (i k) hkT).rescale_P6M (c k) (hc k),
    fun b => ?_, hacc, hD, hord, fun b => ?_⟩
  · exact ((records (i k) hkT).static b).hasCanonicalWindow_rescale_P6M
      (GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _ (hlink (i k) hkT b))
      (c k) (hc k)
  · have hΛδ : p.recenterConstant * q.delta ((F.tower.history (ind k)).time (i k).succ) ≤
        1 / 2 := by
      rw [hprc]
      have h1 := (le_div_iff₀ (by positivity)).1 hkδ
      nlinarith
    have hδρ : q.delta ((F.tower.history (ind k)).time (i k).succ) ^ 2 * q.neckRadius 0 ≤
        1 / (2 * max 1 (3 / c k)) := by
      rw [le_div_iff₀ (by positivity)]
      have h2 := (le_div_iff₀ (by positivity)).1 hkc
      calc q.delta ((F.tower.history (ind k)).time (i k).succ) ^ 2 * q.neckRadius 0 *
            (2 * max 1 (3 / c k)) =
          q.delta ((F.tower.history (ind k)).time (i k).succ) *
            (q.delta ((F.tower.history (ind k)).time (i k).succ) *
              (2 * max 1 (3 / c k) * q.neckRadius 0)) := by ring
        _ ≤ q.delta ((F.tower.history (ind k)).time (i k).succ) * 1 :=
          mul_le_mul_of_nonneg_left h2 hdel0.le
        _ ≤ 1 := by linarith
    have hlt := RetainedCoreHistory.inv_two_mul_sq_lt_static_scale_record_delta_P6M3
      (records (i k) hkT)
      (δ₀ := q.delta ((F.tower.history (ind k)).time (i k).succ)) (ρ₁ := q.neckRadius 0)
      (ρ₀ := 1 / (2 * max 1 (3 / c k))) hΛδ (le_of_eq (congrFun hpδ _))
      (by rw [hpρ]; exact hρa (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0) ht0) hδρ b
    have heq : (2 * (1 / (2 * max 1 (3 / c k))) ^ 2)⁻¹ = 2 * (max 1 (3 / c k)) ^ 2 := by
      have := hSpos.ne'
      field_simp
    rw [heq] at hlt
    have e : (((records (i k) hkT).rescale_P6M (c k) (hc k)).static b).neck.scale =
        c k * ((records (i k) hkT).static b).neck.scale :=
      ((records (i k) hkT).static b).rescale_P6M_scale (c k) (hc k)
    exact lt_of_lt_of_eq (six_lt_rescaled_of_sq_P6H6 (hc k) hlt) e.symm

/-- **G1c（闭合形）**：KNOM supply `hP5L / hδq / hρa` ⇒ `∃ Tmin`，任一 `T₀ ≥ Tmin` 且 lateness
`hlateT` ⇒ `hrec6`（G1a ∘ G1b）。 -/
theorem hrec6_of_knom_P6H6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (recs : ∀ k (i : Fin (F.tower.history k).eventCount),
      GeometricCutoffRecord (F.tower.history k).toHistory i q) (Q : ℕ → ℝ)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (F.tower.history k).eventCount,
        T ≤ (F.tower.history k).time i.succ →
        GeometricCutoffRecord (F.tower.history k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) ∧
      ∀ i hi, (records i hi).nominalRadius = (recs k i).nominalRadius ∧
        (records i hi).delta = (recs k i).delta ∧
        (records i hi).order = (recs k i).order ∧
        (∀ α, HEq ((records i hi).neck α) ((recs k i).neck α)) ∧
        (∀ b, ((records i hi).static b).neck.scale = ((recs k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records i hi).static b).inclusion (((records i hi).static b).witness.cap z) =
            ((recs k i).static b).inclusion (((recs k i).static b).witness.cap z))
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) :
    ∃ Tmin : (ℕ → ℝ) → ℕ → ℝ, ∀ T₀ : (ℕ → ℝ) → ℕ → ℝ, (∀ c n, Tmin c n ≤ T₀ c n) →
    (∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, T₀ c k ≤ (F.tower.history (ind k)).time (i k).succ) →
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale := by
  obtain ⟨Tmin, hT⟩ := hjoint_of_knom_P6H6 recs Q hP5L hδq hρa
  exact ⟨Tmin, fun T₀ hT₀ hlateT => hrec6_of_nomDiag_P6H6 F Q T₀ (hT T₀ hT₀) hlateT⟩

/-! ## 3. G2：consumers -/

/-- **无条件的 4 合取 `hrec` producer（G2c，`_P6H6`）**：固定档 supply
`LateLinkedRecordsSupply_C11E F q`（KNOM / KDIAG / NOMID 共同的 P5L 供给）⇒ `hcapWL_of_records_P6HB`
的 `hrec`（4 合取）**不需要** lateness 与 hOpen：`hrec` 的精度 / 半径 / 阶是**固定**目标
`(εcap, Rcap, mcap)`，阈值 `T` 与 `k` 无关，`Tendsto (c k · Kh.time)` 给出 Ho 时间 `→ ∞`
（`c k · (Ho.time / c k) = Ho.time`），`T ≤ Ho.time (i k).succ` eventually 自动成立。
只有第 5 合取项 `6 < scale` 才引入 `c` 与 event 时间的相容性（`hlateT`）。 -/
theorem hrec_of_P5L_P6H6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q) :
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder := by
  intro ind c hc Kh i hlate εcap Rcap mcap hεcap
  obtain ⟨T, hT⟩ := hP5L Rcap εcap mcap hεcap
  have hev : ∀ᶠ k in atTop, T ≤ (F.tower.history (ind k)).time (i k).succ := by
    filter_upwards [hlate.eventually_ge_atTop T] with k hk
    have e : c k * (Kh k).time (i k).succ = (F.tower.history (ind k)).time (i k).succ :=
      mul_div_cancel₀ _ (hc k).ne'
    exact e ▸ hk
  filter_upwards [hev] with k hk
  obtain ⟨p, -, -, -, -, hD, hacc, hord, records, hlink⟩ := hT (ind k)
  exact ⟨p.rescale_P6N (c k) (hc k), (records (i k) hk).rescale_P6M (c k) (hc k),
    fun b => ((records (i k) hk).static b).hasCanonicalWindow_rescale_P6M
      (GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _ (hlink (i k) hk b))
      (c k) (hc k), hacc, hD, hord⟩

/-- **consumer 0（`hcapWL` 槽，无 lateness）**：`hrec_of_P5L_P6H6` 喂 `hcapWL_of_records_P6HB`。 -/
theorem hcapWL_of_P5L_P6H6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 11) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ C1 C2 : ℝ, Cs ≤ C1 → Cs ≤ C2 →
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          ∀ (b : ((Kh k).event (i k)).RetainedBoundaryIndex) (x : ThreeBall),
            ∃ W : SpatialCanonicalWitness ((Kh k).event (i k)).outputMetric ε C1 C2
              ((Rc.static b).inclusion ((Rc.static b).witness.cap x)),
              W.capTubeHasNeckChart ε := by
  obtain ⟨Cs, hCs, h⟩ := ObservedHistory.hcapWL_of_records_P6HB F hε hε'
  exact ⟨Cs, hCs, fun C1 C2 h1 h2 => h C1 C2 h1 h2 (hrec_of_P5L_P6H6 hP5L)⟩

/-- **consumer 1（`hcapWL` 槽）**：`hrec6` ⇒ `hrec`（`hrec_of_hrec6_P6HE`）⇒ `hcapWL_of_records_P6HB`
的 `hcapWL`。结论 = `hcapWL_of_records_P6HB` 的结论逐字。 -/
theorem hcapWL_of_hrec6_P6H6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hrec6 : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ C1 C2 : ℝ, Cs ≤ C1 → Cs ≤ C2 →
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          ∀ (b : ((Kh k).event (i k)).RetainedBoundaryIndex) (x : ThreeBall),
            ∃ W : SpatialCanonicalWitness ((Kh k).event (i k)).outputMetric ε C1 C2
              ((Rc.static b).inclusion ((Rc.static b).witness.cap x)),
              W.capTubeHasNeckChart ε := by
  obtain ⟨Cs, hCs, h⟩ := ObservedHistory.hcapWL_of_records_P6HB F hε hε'
  exact ⟨Cs, hCs, fun C1 C2 h1 h2 => h C1 C2 h1 h2 (hrec_of_hrec6_P6HE F hrec6)⟩

/-- **consumer 1'（KNOM 闭合 → `hcapWL`）**：`hrec6_of_knom_P6H6` 喂 `hcapWL_of_hrec6_P6H6`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (recs : ∀ k (i : Fin (F.tower.history k).eventCount),
      GeometricCutoffRecord (F.tower.history k).toHistory i q) (Q : ℕ → ℝ)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (F.tower.history k).eventCount,
        T ≤ (F.tower.history k).time i.succ →
        GeometricCutoffRecord (F.tower.history k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) ∧
      ∀ i hi, (records i hi).nominalRadius = (recs k i).nominalRadius ∧
        (records i hi).delta = (recs k i).delta ∧
        (records i hi).order = (recs k i).order ∧
        (∀ α, HEq ((records i hi).neck α) ((recs k i).neck α)) ∧
        (∀ b, ((records i hi).static b).neck.scale = ((recs k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records i hi).static b).inclusion (((records i hi).static b).witness.cap z) =
            ((recs k i).static b).inclusion (((recs k i).static b).witness.cap z))
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0))
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ Tmin : (ℕ → ℝ) → ℕ → ℝ, ∀ T₀ : (ℕ → ℝ) → ℕ → ℝ, (∀ c n, Tmin c n ≤ T₀ c n) →
    (∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, T₀ c k ≤ (F.tower.history (ind k)).time (i k).succ) →
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ C1 C2 : ℝ, Cs ≤ C1 → Cs ≤ C2 →
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          ∀ (b : ((Kh k).event (i k)).RetainedBoundaryIndex) (x : ThreeBall),
            ∃ W : SpatialCanonicalWitness ((Kh k).event (i k)).outputMetric ε C1 C2
              ((Rc.static b).inclusion ((Rc.static b).witness.cap x)),
              W.capTubeHasNeckChart ε := by
  obtain ⟨Tmin, h⟩ := hrec6_of_knom_P6H6 recs Q hP5L hδq hρa
  exact ⟨Tmin, fun T₀ hT₀ hlateT => hcapWL_of_hrec6_P6H6 F hε hε' (h T₀ hT₀ hlateT)⟩

/-- **consumer 2（`hcenE` 的 `hrec6` 槽）**：`hrec6_of_nomDiag_P6H6` 喂 `hcenE_of_noShortcut_P6HE`；
剩余 binder = `hCs1 hCs2`（CEIL3）+ G1b 的 `hjoint hlateT`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (Q : ℕ → ℝ) (T₀ : (ℕ → ℝ) → ℕ → ℝ) {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ}
    (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hCs1 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C1)
    (hCs2 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C2)
    (hjoint : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ), (∀ k, 0 < c k) →
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ c n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
        (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
        (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧ (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
        (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤
          ((recordsK n i hi).static b).neck.scale))
    (hlateT : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, T₀ c k ≤ (F.tower.history (ind k)).time (i k).succ) :=
  hcenE_of_noShortcut_P6HE (Ctime := Ctime) (C1f := C1f) (C2f := C2f) (m := m) (kk := kk) F hε hε'
    hCs1 hCs2 (hrec6_of_nomDiag_P6H6 F Q T₀ hjoint hlateT)

/-- **consumer 3（G1d → `hcenE` 的 `hrec6` 槽 ∧ `hcapWL` 槽）**：`hrec6_of_P5L_compat_P6H6` 同时喂
`hcenE_of_noShortcut_P6HE`（`hrec6` 槽）与 `hcapWL_of_hrec6_P6H6`。剩余 binder = `hCs1 hCs2`（CEIL3）
+ `hcompat`（PROVISIONAL）+ P5L supply / `hδq` / `hρa`（树内 S1+S2 供给）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ}
    (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hCs1 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C1)
    (hCs2 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C2)
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0))
    (hcompat : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, q.delta ((F.tower.history (ind k)).time (i k).succ) ≤
          1 / (2 * max 1 (3 / c k) * q.neckRadius 0)) :=
  And.intro
    (hcenE_of_noShortcut_P6HE (Ctime := Ctime) (C1f := C1f) (C2f := C2f) (m := m) (kk := kk) F
      hε hε' hCs1 hCs2 (hrec6_of_P5L_compat_P6H6 hP5L hδq hρa hcompat))
    (hcapWL_of_hrec6_P6H6 F hε hε' (hrec6_of_P5L_compat_P6H6 hP5L hδq hρa hcompat))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
