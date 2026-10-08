import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapContractsLocP6KT2

/-!
# L5（J9 部分）：截断 J9 ⇐ 先验 `TimeDerivativeSupply_C11E`，局部阈值（O-CH11-KTRUNC2，后缀 `_P6KT2`）

`hgap{J,J8}_loc_P6KT2` 的 J9 合取（原尺度 `Ho n = F.tower.history (ind n)`，终点 `min (time j.succ) (Tno n)`）
在**局部阈值** `Qs n ≥ ρ(tK n)⁻²` 下由先验供给付清：先验只在 `R > ρ(t)⁻²` 给 `|∂ₜR| ≤ Ctime·R²`，
`ρ` 反单调 ⇒ `t < tK n` 时 `ρ(t)⁻² ≤ ρ(tK n)⁻² ≤ Qs n`。取 `tK := Tno`、
`Qs_loc n := max ((n+1)/c n) (ρ(Tno n)²)⁻¹`（KSLABK 推荐形，horizon → Tno）即 J9 截断形逐字。
这是 KSLABK G1 `hslabK_of_supply_P6KS`（天花板在 horizon）的截断孪生；J6 = (SEP-ρ⁺@Tno) 不在本文件。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- 反单调正半径 ⇒ 局部天花板：`0 ≤ t ≤ H` 处 `(ρ t²)⁻¹ ≤ (ρ H²)⁻¹ ≤ Q`（`_P6KT2`）。 -/
theorem ceil_of_antitone_P6KT2 {ρ : ℝ → ℝ} (hρ : AntitoneOn ρ (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < ρ t) {H Q : ℝ} (hQ : (ρ H ^ 2)⁻¹ ≤ Q) {t : ℝ} (ht0 : 0 ≤ t)
    (htH : t ≤ H) : (ρ t ^ 2)⁻¹ ≤ Q := by
  have hH0 : 0 ≤ H := ht0.trans htH
  have hle : ρ H ≤ ρ t := hρ (mem_Ici.mpr ht0) (mem_Ici.mpr hH0) htH
  have hsq : ρ H ^ 2 ≤ ρ t ^ 2 := pow_le_pow_left₀ (hpos H hH0).le hle 2
  exact (inv_anti₀ (pow_pos (hpos H hH0) 2) hsq).trans hQ

/-- **截断 J9 ⇐ 先验供给（局部阈值，`_P6KT2`）**：`(ρ(tK n)²)⁻¹ ≤ Qs n` ⇒ 每个 event slab 在终点
`min (time j.succ) (tK n)` 前的导数界（`hgapJ_loc_P6KT2` J9 合取形，原尺度塔帧）。 -/
theorem hslabKT_of_supply_P6KT2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀)
    (hρ : AntitoneOn ρ (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < ρ t) (ind : ℕ → ℕ) (Qs tK : ℕ → ℝ)
    (hQs : ∀ n, (ρ (tK n) ^ 2)⁻¹ ≤ Qs n) :
    ∀ n (j : Fin (F.tower.history (ind n)).eventCount),
      ((F.tower.history (ind n)).toHistory.event j).incoming.DerivativeBoundBefore Ctime₀ (Qs n)
        (min ((F.tower.history (ind n)).time j.succ) (tK n)) := by
  intro n j y t ht hR
  have h0 : 0 ≤ t := by
    have hz : (F.tower.history (ind n)).time 0 ≤ (F.tower.history (ind n)).time j.castSucc :=
      (F.tower.history (ind n)).time_strictMono.monotone (Fin.zero_le _)
    rw [(F.tower.history (ind n)).time_zero] at hz
    exact hz.trans ht.1.le
  have htK : t ≤ tK n := (ht.2.trans_le (min_le_right _ _)).le
  have hceil := ceil_of_antitone_P6KT2 hρ hpos (hQs n) h0 htK
  refine (hTD.1 (ind n) j y t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    (hceil.trans_lt hR)).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (sq_nonneg _)

/-- consumer：`tK := Tno`、`Qs_loc n := max ((n+1)/c n) (ρ(Tno n)²)⁻¹` ⇒ `hgapJ_loc_P6KT2` 的 J9 合取逐字
（`Ho n = F.tower.history (ind n)`，终点 `min ((Ho n).time j.succ) (Tno n : ℝ)`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0} (hTD : TimeDerivativeSupply_C11E F ρ Ctime)
    (hC : Ctime ≤ Ctime₀) (hρ : AntitoneOn ρ (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < ρ t)
    (ind : ℕ → ℕ) (Tno : ∀ k, Icc (0 : ℝ) (F.tower.history (ind k)).toHistory.horizon)
    (c : ℕ → ℝ) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (ρ (Tno n) ^ 2)⁻¹
    ∀ n (j : Fin (Ho n).eventCount),
      ((Ho n).toHistory.event j).incoming.DerivativeBoundBefore Ctime₀ (Qs n)
        (min ((Ho n).time j.succ) (Tno n : ℝ)) :=
  hslabKT_of_supply_P6KT2 hTD hC hρ hpos ind _ (fun n => (Tno n : ℝ)) fun _ => le_max_right _ _

end GC.LongTime.Ch11
