import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaBudgetLevelC11Q7

/-!
# nodeR 的 block 绑定与 lookahead 覆盖（O-CH11-KWRAP G3，后缀 `_C11Q7`）

R-C11-6 D-6（审稿 Q2(R-a)）：`nodeR := nr(block)/100` 须说明 block；事件所在较早 block 的 `nr` 偏大，未必
`≤ r`。审稿给的一个可用选择是 query-time 二进块 `R_k = nr(2^k)/100`，`k = k(t)`；[推断] W-step lookahead
须覆盖事件服务的所有 query windows（半时间窗 `t ∈ [s, 2s]`）。

G0 (b) 核查：FINEPACK `eventNodeData_of_blocks_C11Q6` 取 `nodeR = rad(m+1)/100`，`m` = event 所在 astra 块
（不是 `k(t)`），`rad(m+1)` = lookahead `rNext_m`；astra m-i 子句给**覆盖子句**
`∀ T ∈ [s, 2s], rad(m+1) ≤ nr T`。本文件把 D-6 的要求落成与 block 选择无关的覆盖形，并证明两条路线都是它的实例：

* `mem_lookahead_of_seed_C11Q7`：种子 `(t, r)`（`2r² < t`）的事件 `s ∈ [t − r², t]` ⇒ `t ∈ [s, 2s]`；
* **`nodeR_le_of_lookahead_C11Q7`**：覆盖子句 + 种子尺度 guard `nr t/100 ≤ r` + `nr t/100 ≤ ϱ₀`
  ⇒ `nodeR ≤ nr(t)/100`、`nodeR ≤ r`、`nodeR ≤ ϱ₀`；
* query-time 路线：`queryBlockRadius_le_C11Q7`（`R_{k(t)} ≤ nr(t)/100`）、`queryBlock_two_C11Q7`
  （`t ∈ [s, 2s] ⇒ k(t) ∈ {k(s), k(s)+1}`）、`queryBlock_adjacent_C11Q7`（相邻 query 块确实出现：只预算事件
  当前块会漏）、`queryBlock_ge_lookahead_C11Q7`（`R_{k(s)+1} ≤ R_{k(t)}`）、
  **`dyadicLookahead_covers_C11Q7`**（单个事件时刻 lookahead 半径 `nr(2^{k(s)+1})` 满足覆盖子句）；
* D-6 (i) 测试分支 guard：`seedGuard_of_test_C11Q7`（`nr(v)/100 ≤ ρ < r/100`、`v ≤ t` ⇒ `nr(t)/100 ≤ r`）。

结论：不改绑 FINEPACK 的 node 数据（chooser 对 `rTerm` 不单调，改绑到 `R_{k(t)}` 需块请求在两处支配、现有塔不生产）；
FINEPACK 的覆盖子句由 astra 生产（`exists_blockData_C11Q6` 的 `hnrT`），D-6 的实质要求已满足。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 覆盖形 -/

/-- 种子 `(t, r)`（`2r² < t`）在时钟窗 `[t − r², t]` 内的事件 `s` 只服务 `t ∈ [s, 2s]`。 -/
theorem mem_lookahead_of_seed_C11Q7 {t r s : ℝ} (hr : 2 * r ^ 2 < t) (hlo : t - r ^ 2 ≤ s)
    (hst : s ≤ t) : t ∈ Icc s (2 * s) :=
  ⟨hst, by nlinarith [sq_nonneg r]⟩

/-- **lookahead 覆盖 ⇒ nodeR 控制**（D-6）：`∀ T ∈ [s, 2s], rad ≤ nr T` 且种子服务 `t ∈ [s, 2s]`，
尺度 guard `nr t/100 ≤ r` 与测试球 `nr t/100 ≤ ϱ₀` ⇒ `rad/100 ≤ nr(t)/100 ≤ min(r, ϱ₀)`。 -/
theorem nodeR_le_of_lookahead_C11Q7 {nr : ℝ → ℝ} {rad s t r ϱ₀ : ℝ}
    (hcov : ∀ T ∈ Icc s (2 * s), rad ≤ nr T) (ht : t ∈ Icc s (2 * s))
    (hscale : nr t / 100 ≤ r) (hϱ₀ : nr t / 100 ≤ ϱ₀) :
    rad / 100 ≤ nr t / 100 ∧ rad / 100 ≤ r ∧ rad / 100 ≤ ϱ₀ := by
  have h := hcov t ht
  refine ⟨by linarith, by linarith, by linarith⟩

/-- 种子形：事件 `s ∈ [t − r², t]`（`2r² < t`）+ 覆盖子句 ⇒ nodeR 控制。 -/
theorem nodeR_le_of_seed_C11Q7 {nr : ℝ → ℝ} {rad s t r ϱ₀ : ℝ}
    (hcov : ∀ T ∈ Icc s (2 * s), rad ≤ nr T) (hr : 2 * r ^ 2 < t) (hlo : t - r ^ 2 ≤ s)
    (hst : s ≤ t) (hscale : nr t / 100 ≤ r) (hϱ₀ : nr t / 100 ≤ ϱ₀) :
    rad / 100 ≤ nr t / 100 ∧ rad / 100 ≤ r ∧ rad / 100 ≤ ϱ₀ :=
  nodeR_le_of_lookahead_C11Q7 hcov (mem_lookahead_of_seed_C11Q7 hr hlo hst) hscale hϱ₀

/-! ## 2. query-time 二进块路线 -/

/-- `R_{k(t)} = nr(2^{k(t)})/100 ≤ nr(t)/100`（`t ≤ 2^{k(t)}`，`nr` antitone）。 -/
theorem queryBlockRadius_le_C11Q7 {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0)) {t : ℝ}
    (ht : 0 ≤ t) : nr (blockTime_C11Q5 (blockIndex_C11Q5 t)) / 100 ≤ nr t / 100 := by
  have h := hanti (Set.mem_Ici.mpr ht) (Set.mem_Ici.mpr (blockTime_pos_C11Q5 _).le)
    (le_blockTime_C11Q5 t)
  linarith

/-- query-time 选择也满足 D-6 不等式：`R_{k(t)} ≤ nr(t)/100 ≤ min(r, ϱ₀)`。 -/
theorem queryBlockNode_le_C11Q7 {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0)) {t r ϱ₀ : ℝ}
    (ht : 0 ≤ t) (hscale : nr t / 100 ≤ r) (hϱ₀ : nr t / 100 ≤ ϱ₀) :
    nr (blockTime_C11Q5 (blockIndex_C11Q5 t)) / 100 ≤ r ∧
      nr (blockTime_C11Q5 (blockIndex_C11Q5 t)) / 100 ≤ ϱ₀ := by
  have h := queryBlockRadius_le_C11Q7 hanti ht
  exact ⟨h.trans hscale, h.trans hϱ₀⟩

/-- 事件 `s` 服务的 query 块只有两个：`t ∈ [s, 2s] ⇒ k(t) ∈ {k(s), k(s)+1}`。 -/
theorem queryBlock_two_C11Q7 {s t : ℝ} (hs : 0 < s) (ht : t ∈ Icc s (2 * s)) :
    blockIndex_C11Q5 t = blockIndex_C11Q5 s ∨ blockIndex_C11Q5 t = blockIndex_C11Q5 s + 1 := by
  have h1 := blockIndex_le_C11Q5 hs ht.1
  have h2 := blockIndex_le_succ_C11Q5 (hs.trans_le ht.1) ht.2
  omega

/-- 相邻 query 块确实出现（`s = 1`、`t = 2`）：只预算事件当前块的请求会漏掉 `k(s)+1`。 -/
theorem queryBlock_adjacent_C11Q7 :
    ∃ s t : ℝ, 0 < s ∧ t ∈ Icc s (2 * s) ∧ blockIndex_C11Q5 t = blockIndex_C11Q5 s + 1 := by
  have h0 := Int.clog_zpow (R := ℝ) (b := 2) (by norm_num) 0
  have h1 := Int.clog_zpow (R := ℝ) (b := 2) (by norm_num) 1
  simp only [Nat.cast_ofNat, zpow_zero, zpow_one] at h0 h1
  refine ⟨1, 2, one_pos, ⟨by norm_num, by norm_num⟩, ?_⟩
  unfold blockIndex_C11Q5
  rw [h0, h1]
  norm_num

/-- 单个 lookahead 半径支配两个 query 块：`t ∈ [s, 2s] ⇒ nr(2^{k(s)+1}) ≤ nr(2^{k(t)})`。 -/
theorem queryBlock_ge_lookahead_C11Q7 {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0)) {s t : ℝ}
    (hs : 0 < s) (ht : t ∈ Icc s (2 * s)) :
    nr (blockTime_C11Q5 (blockIndex_C11Q5 s + 1)) ≤ nr (blockTime_C11Q5 (blockIndex_C11Q5 t)) := by
  have h2 := blockIndex_le_succ_C11Q5 (hs.trans_le ht.1) ht.2
  have hle : blockTime_C11Q5 (blockIndex_C11Q5 t) ≤ blockTime_C11Q5 (blockIndex_C11Q5 s + 1) :=
    zpow_le_zpow_right₀ (by norm_num) h2
  exact hanti (Set.mem_Ici.mpr (blockTime_pos_C11Q5 _).le)
    (Set.mem_Ici.mpr (blockTime_pos_C11Q5 _).le) hle

/-- **二进 lookahead 满足覆盖子句**：事件时刻 `s` 的单个半径 `nr(2^{k(s)+1})` 对 `[s, 2s]` 全体 `T` 成立
`≤ nr T`——D-6 的 query-time 选择（在事件时刻按下一块预算）是 FINEPACK 覆盖子句的一个实例。 -/
theorem dyadicLookahead_covers_C11Q7 {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0)) {s : ℝ}
    (hs : 0 < s) : ∀ T ∈ Icc s (2 * s), nr (blockTime_C11Q5 (blockIndex_C11Q5 s + 1)) ≤ nr T := by
  intro T hT
  have h1 := le_blockTime_C11Q5 s
  have h2 : blockTime_C11Q5 (blockIndex_C11Q5 s + 1) =
      2 * blockTime_C11Q5 (blockIndex_C11Q5 s) := by
    unfold blockTime_C11Q5
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hT0 : 0 ≤ T := by linarith [hT.1]
  exact hanti (Set.mem_Ici.mpr hT0) (Set.mem_Ici.mpr (blockTime_pos_C11Q5 _).le)
    (by linarith [hT.2])

/-! ## 3. D-6 (i) 测试分支 guard -/

/-- **测试分支导出种子 guard**：`nr(v)/100 ≤ ρ < r/100`、`0 < ρ`、`0 ≤ v ≤ t` ⇒ `nr(t)/100 ≤ r`
（`nr` antitone；空真只用于 `r < nr(t)/100` 的测试分支，不倒灌全称合同）。 -/
theorem seedGuard_of_test_C11Q7 {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0)) {v t ρ r : ℝ}
    (hv : 0 ≤ v) (hvt : v ≤ t) (hρ : 0 < ρ) (hlow : nr v / 100 ≤ ρ) (hup : ρ < r / 100) :
    nr t / 100 ≤ r := by
  have h := hanti (Set.mem_Ici.mpr hv) (Set.mem_Ici.mpr (hv.trans hvt)) hvt
  linarith

/-! ## 4. 与 FINEPACK 的对齐（consumer） -/

/-- **对齐（FINEPACK event node）**：`hev` 的覆盖子句（`rad(m+1) ≤ nr T`，`T ∈ [s, 2s]`，astra m-i 子句）+
种子 `(t, r)` 的时钟窗 + G6 尺度 guard ⇒ `nodeR = rad(m+1)/100 ≤ min(r, ϱ₀)`（`eventNodeData_of_blocks_C11Q6`
里 `nodeR ≤ r` 与受控球单调所需的两条）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) (rad : ℕ → ℝ) (m : ℕ)
    {s t r ϱ₀ : ℝ} (hcov : ∀ T ∈ Icc s (2 * s), rad (m + 1) ≤ N.params.neckRadius T)
    (hr : 2 * r ^ 2 < t) (hlo : t - r ^ 2 ≤ s) (hst : s ≤ t)
    (hscale : N.params.neckRadius t / 100 ≤ r) (hϱ₀ : N.params.neckRadius t / 100 ≤ ϱ₀) :
    rad (m + 1) / 100 ≤ r ∧ rad (m + 1) / 100 ≤ ϱ₀ :=
  (nodeR_le_of_seed_C11Q7 hcov hr hlo hst hscale hϱ₀).2

/-- **对齐（D-6 选择 ⇒ FINEPACK 覆盖形）**：native 数据下，事件时刻 `s` 的二进 lookahead 半径
`nr(2^{k(s)+1})` 满足 FINEPACK `hev` 的覆盖子句形；于是 nodeR 取它也给出 D-6 不等式。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) {s t r ϱ₀ : ℝ}
    (hs : 0 < s) (hr : 2 * r ^ 2 < t) (hlo : t - r ^ 2 ≤ s) (hst : s ≤ t)
    (hscale : N.params.neckRadius t / 100 ≤ r) (hϱ₀ : N.params.neckRadius t / 100 ≤ ϱ₀) :
    (∀ T ∈ Icc s (2 * s),
      N.params.neckRadius (blockTime_C11Q5 (blockIndex_C11Q5 s + 1)) ≤ N.params.neckRadius T) ∧
    N.params.neckRadius (blockTime_C11Q5 (blockIndex_C11Q5 s + 1)) / 100 ≤ r ∧
    N.params.neckRadius (blockTime_C11Q5 (blockIndex_C11Q5 s + 1)) / 100 ≤ ϱ₀ := by
  have hcov := dyadicLookahead_covers_C11Q7 N.radius_antitone hs
  exact ⟨hcov, (nodeR_le_of_seed_C11Q7 hcov hr hlo hst hscale hϱ₀).2⟩

end GC.LongTime.Ch11
