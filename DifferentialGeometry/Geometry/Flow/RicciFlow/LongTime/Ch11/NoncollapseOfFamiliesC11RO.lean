import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.NoncollapseProfileC11RO
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RegularObservationNoncollapseC11RO

set_option autoImplicit false

/-!
# O-CH11-REPROVE-O (G4)：S6 ⇐ 逐层 canonical cutoff family（G3 ∘ G2）

G3 `exists_regular_observation_noncollapsed_C11RO` 在每个层 `n` 取 `B := n + 1`，得到只依赖
`(P, g, ε, Λ, n)` 的 caps `δmax n, ρmax n, εcap n, Dcap n, mcap n` 与 `κ n > 0`；G2
`noncollapseSupply_iff_levels_C11RO` 把逐层 noncollapse 变成 S6。于是：

* `exists_level_noncollapse_of_families_C11RO`：存在 `εbar > 0`，对 `0 < ε < 1/11`、`ε ≤ εbar`、
  `0 < Λ`，有逐层 caps 与 `κ : ℕ → ℝ`（正，**与 flow 无关**），使任何 `F : RawSurgery P g`
  只要每层 history `n` 带一个满足第 `n` 层 caps 的 canonical cutoff record family，就有
  `(F.tower.history n).NoncollapsedBefore (κ n) ε n`；
* `exists_noncollapseSupply_of_families_C11RO`：同前提 ⇒ `∃ κ', NoncollapseSupply_C11S F κ' ε`（S6）。

限制（写进 G3 design）：caps 随 `B = n + 1` 变化（`εcap`、`δmax`、`ρmax` 一般变小，`Dcap`、`mcap`
变大），一个固定的 `q` 一般不能同时满足所有层，所以 SKEL bundle 的 `records : CutoffRecords_C11S F q`
不能直接喂进来；astra 用 affine join（`SN/AffineJoinNoncollapse.lean:27`）把旧 history 与在当前时刻
重新起算的尾段拼起来，尾段才用 G3（初始数据 = 当时的 stage metric）。
-/

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

/-- **逐层 noncollapse ⇐ 逐层 canonical family**：caps 与 κ 只依赖 `(P, g, ε, Λ)` 与层号。 -/
theorem exists_level_noncollapse_of_families_C11RO (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ εbar : ℝ, 0 < εbar ∧ ∀ ε Λ : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar → 0 < Λ →
    ∃ (δmax ρmax εcap Dcap : ℕ → ℝ) (mcap : ℕ → ℕ) (κ : ℕ → ℝ),
      (∀ n, 0 < δmax n ∧ 0 < ρmax n ∧ 0 < εcap n ∧ 0 < Dcap n ∧ 0 < κ n) ∧
      ∀ F : GC.Interface.RawSurgery P g,
        (∀ n : ℕ, ∃ (p₀ : CutoffParameters) (δb ρb : ℝ) (p : CutoffParameters)
          (records : ∀ i, GeometricCutoffRecord (F.tower.history n).toHistory i p),
          p₀.modelAccuracy ≤ εcap n ∧ Dcap n ≤ p₀.modelRadius ∧ mcap n ≤ p₀.modelOrder ∧
          δb ≤ δmax n ∧ ρb ≤ ρmax n ∧ p₀.recenterConstant ≤ Λ ∧
          (F.tower.history n).IsCanonicalCutoffRecordFamily p₀ δb ρb records) →
        ∀ n : ℕ, (F.tower.history n).NoncollapsedBefore (κ n) ε n := by
  obtain ⟨εbar, hεbar, hreg⟩ := GC.GeneralFlow.exists_regular_observation_noncollapsed_C11RO P g
  refine ⟨εbar, hεbar, fun ε Λ hε hε' hεb hΛ => ?_⟩
  have hlev := fun n : ℕ =>
    hreg ((n : ℝ) + 1) ε Λ (by positivity) hε hε' hεb hΛ
  choose δmax ρmax εcap Dcap mcap κ hδ hρ hεc hD hκ hmain using hlev
  refine ⟨δmax, ρmax, εcap, Dcap, mcap, κ, fun n => ⟨hδ n, hρ n, hεc n, hD n, hκ n⟩, ?_⟩
  intro F hfam n
  obtain ⟨p₀, δb, ρb, p, records, hacc, hDc, hm, hδb, hρb, hΛp, hfamily⟩ := hfam n
  have hhor : (F.tower.history n).horizon < (n : ℝ) + 1 := by
    rw [F.tower.horizon_eq]
    exact lt_add_one _
  have hnc := hmain n p₀ δb ρb hacc hDc hm hδb hρb hΛp (F.tower.history n)
    (F.tower.initial n) p records hhor hfamily
  rw [F.tower.horizon_eq] at hnc
  exact hnc

/-- **S6 ⇐ 逐层 canonical family**（G4 ∘ G2）。 -/
theorem exists_noncollapseSupply_of_families_C11RO (P : OrientedThreeStage.{u})
    (g : P.Metric) :
    ∃ εbar : ℝ, 0 < εbar ∧ ∀ ε Λ : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar → 0 < Λ →
    ∃ (δmax ρmax εcap Dcap : ℕ → ℝ) (mcap : ℕ → ℕ),
      (∀ n, 0 < δmax n ∧ 0 < ρmax n ∧ 0 < εcap n ∧ 0 < Dcap n) ∧
      ∀ F : GC.Interface.RawSurgery P g,
        (∀ n : ℕ, ∃ (p₀ : CutoffParameters) (δb ρb : ℝ) (p : CutoffParameters)
          (records : ∀ i, GeometricCutoffRecord (F.tower.history n).toHistory i p),
          p₀.modelAccuracy ≤ εcap n ∧ Dcap n ≤ p₀.modelRadius ∧ mcap n ≤ p₀.modelOrder ∧
          δb ≤ δmax n ∧ ρb ≤ ρmax n ∧ p₀.recenterConstant ≤ Λ ∧
          (F.tower.history n).IsCanonicalCutoffRecordFamily p₀ δb ρb records) →
        ∃ κ : ℝ → ℝ, NoncollapseSupply_C11S F κ ε := by
  obtain ⟨εbar, hεbar, h⟩ := exists_level_noncollapse_of_families_C11RO P g
  refine ⟨εbar, hεbar, fun ε Λ hε hε' hεb hΛ => ?_⟩
  obtain ⟨δmax, ρmax, εcap, Dcap, mcap, κ, hpos, hmain⟩ := h ε Λ hε hε' hεb hΛ
  refine ⟨δmax, ρmax, εcap, Dcap, mcap,
    fun n => ⟨(hpos n).1, (hpos n).2.1, (hpos n).2.2.1, (hpos n).2.2.2.1⟩, ?_⟩
  intro F hfam
  exact noncollapseSupply_iff_levels_C11RO.mpr fun n =>
    ⟨κ n, (hpos n).2.2.2.2, hmain F hfam n⟩

/-! ## consumer -/

/-- consumer：同一 bundle 的 records 若在每层恰好满足第 `n` 层 caps（`p₀ := q`），S6 成立；
canonical window 条款就是 S3。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ εbar : ℝ, 0 < εbar ∧ ∀ ε Λ : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar → 0 < Λ →
    ∃ (δmax ρmax εcap Dcap : ℕ → ℝ) (mcap : ℕ → ℕ),
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
        (records : CutoffRecords_C11S F q),
        CanonicalWindowsSupply_C11S records →
        (∀ n, q.modelAccuracy ≤ εcap n ∧ Dcap n ≤ q.modelRadius ∧ mcap n ≤ q.modelOrder ∧
          q.recenterConstant ≤ Λ ∧
          (∀ i : Fin (F.tower.history n).eventCount,
            q.delta ((F.tower.history n).time i.succ) ≤ δmax n) ∧
          ∀ i : Fin (F.tower.history n).eventCount,
            q.neckRadius ((F.tower.history n).time i.succ) ≤ ρmax n) →
        ∃ κ : ℝ → ℝ, NoncollapseSupply_C11S F κ ε := by
  obtain ⟨εbar, hεbar, h⟩ := exists_noncollapseSupply_of_families_C11RO P g
  refine ⟨εbar, hεbar, fun ε Λ hε hε' hεb hΛ => ?_⟩
  obtain ⟨δmax, ρmax, εcap, Dcap, mcap, -, hmain⟩ := h ε Λ hε hε' hεb hΛ
  refine ⟨δmax, ρmax, εcap, Dcap, mcap, fun F q records hwin hcap => hmain F fun n => ?_⟩
  obtain ⟨hacc, hD, hm, hΛq, hδq, hρq⟩ := hcap n
  exact ⟨q, δmax n, ρmax n, q, records n, hacc, hD, hm, le_rfl, le_rfl, hΛq,
    rfl, rfl, rfl, rfl, rfl, hwin n, hδq, hρq⟩

end GC.LongTime.Ch11
