import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepRhoDiagP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3

/-!
# 前缀 Dt ⇐ profile 供给：重标度 K 帧（O-CH11-HNOT-LOCALDT G5，后缀 `_P6HN`）

KSLABK G1（`P6KernelSlabKSupplyP6KS`）已在 K 帧 `K n = (Ho n).rescale_P6N (c n)` 付清**全 `Fin.last` / 到
horizon** 形的 (D1)(D2)（天花板取 `horizon`）。本文件给出 HNOT G2 / KSLABK 截断形槽用的**前缀形**在同一
K 帧上的付款（天花板只取在求值时刻）：
* `prefixDt_rescale_P6HN`：原尺度 `Ho = F.tower.history m`，K 帧时刻 `t̃`（原尺度 `c·t̃`），
  `EventSlabsDerivative C (c·(ρ(c·t̃)²)⁻¹) j.castSucc` 与 slab `j` 的
  `DerivativeBoundBefore C (c·(ρ(c·t̃)²)⁻¹) t̃`。证明 = 原尺度 `prefixDt_of_timeDerivativeSupply_P6HN`
  + 树内重标度 `eventSlabsDerivative_rescale_P6X3` / `derivativeBoundBefore_rescale_P6X3`
  （`Ctime` 不变、阈值 ×c）。
* `prefixDt_rescale_seq_P6HN`：序列形，结论 = G2 主形 `hnotK_of_capWindowWitness_theta_P6HN` 的两条前缀 Dt
  槽（`K n`、`Q n := c n·(ρ(c n·t n)²)⁻¹`）逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **前缀 Dt，K 帧（`_P6HN`，PROVED）**。 -/
theorem prefixDt_rescale_P6HN {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {C : ℝ≥0}
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius C)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (m : ℕ) {c : ℝ} (hc : 0 < c)
    (j : Fin (F.tower.history m).eventCount) {t : ℝ}
    (hjt : ((F.tower.history m).rescale_P6N c hc).time j.castSucc < t)
    (htj : t ≤ ((F.tower.history m).rescale_P6N c hc).time j.succ) :
    ((F.tower.history m).rescale_P6N c hc).EventSlabsDerivative C
        (c * (q.neckRadius (c * t) ^ 2)⁻¹) j.castSucc ∧
      (((F.tower.history m).rescale_P6N c hc).toHistory.event j).incoming.DerivativeBoundBefore C
        (c * (q.neckRadius (c * t) ^ 2)⁻¹) t := by
  rw [RetainedCoreHistory.rescale_P6N_time] at hjt htj
  have hjt' : (F.tower.history m).time j.castSucc < c * t := by
    rw [div_lt_iff₀ hc] at hjt
    linarith
  have htj' : c * t ≤ (F.tower.history m).time j.succ := by
    rw [le_div_iff₀ hc] at htj
    linarith
  obtain ⟨h1, h2⟩ := prefixDt_of_timeDerivativeSupply_P6HN hTD hanti m j hjt' htj'
  refine ⟨(F.tower.history m).eventSlabsDerivative_rescale_P6X3 hc h1, ?_⟩
  have h := ((F.tower.history m).toHistory.event j).incoming.derivativeBoundBefore_rescale_P6X3
    hc h2
  rwa [mul_div_cancel_left₀ t hc.ne'] at h

/-- **序列形（`_P6HN`，PROVED）**：`K n = (F.tower.history (ind n)).rescale_P6N (c n)`，
`Q n := c n·(ρ(c n·t n)²)⁻¹`；结论 = G2 主形的两条前缀 Dt 槽逐字。 -/
theorem prefixDt_rescale_seq_P6HN {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {C : ℝ≥0}
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius C)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (ind : ℕ → ℕ) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    {j : ∀ n, Fin (F.tower.history (ind n)).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time (j n).castSucc < t n)
    (htj : ∀ n, t n < ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time (j n).succ) :
    (∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).EventSlabsDerivative C
        (c n * (q.neckRadius (c n * t n) ^ 2)⁻¹) (j n).castSucc) ∧
    (∀ n, (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.event
        (j n)).incoming.DerivativeBoundBefore C (c n * (q.neckRadius (c n * t n) ^ 2)⁻¹) (t n)) :=
  ⟨fun n => (prefixDt_rescale_P6HN hTD hanti (ind n) (hc n) (j n) (hjt n) (htj n).le).1,
    fun n => (prefixDt_rescale_P6HN hTD hanti (ind n) (hc n) (j n) (hjt n) (htj n).le).2⟩

/-- consumer（`_P6HN`）：K 帧阈值 `Q n = c n·(ρ(c n·t n)²)⁻¹ > 0`（G2 主形的 `0 < Q n` 槽）。 -/
example {q : CutoffParameters} {c t : ℕ → ℝ} (hc : ∀ n, 0 < c n) (ht : ∀ n, 0 ≤ t n) :
    ∀ n, 0 < c n * (q.neckRadius (c n * t n) ^ 2)⁻¹ := fun n =>
  mul_pos (hc n) (inv_pos.mpr (pow_pos (q.neckRadius_pos _
    (mul_nonneg (hc n).le (ht n))) 2))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
