import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DbbMinRescaleP6KT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelBodyTruncP6KT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscaleKSepRhoP6HN

set_option autoImplicit false

/-!
# 截断形 kernel 槽 ⇐ 先验 `TimeDerivativeSupply_C11E`（O-CH11-KTRUNC1 G4，后缀 `_P6KT`）

KSLABK G1（`P6KernelSlabKSupplyP6KS`）的截断孪生：hQ 的范围从 `t < horizon` 改成 `t < tK`，
天花板因而只需取在截断点 `tK`（下游 `tK := Tn`，原尺度 `Tno`），不再取在 `horizon`
（KSLABK state (3)：`horizon_n − t_n` 在冻结 `∀ ind` 下无界）。
* 塔帧点态：`eventSlabsDerivT_of_supply_P6KT` / `finalSlabDerivT_of_supply_P6KT`；
* hgapJ 元组（原尺度 `Ho n = F.tower.history (ind n)`）截断形：`hslabKT_of_supply_P6KT`
  （`(ρ(tKo n)²)⁻¹ ≤ Qs n` + `ρ` 反单调正）；
* K 帧（`K n = (Ho n).rescale_P6N (c n)`）：`hkernelDtT_of_supply_P6KT` 给 G1 `NotKBodyT_P6KT` 的 `hslabK`
  槽与 `FinalBodyT_P6KT` 的 (D1)(D2) 槽（阈值 `c·Qo`、截断点 `tKo/c`；重标度用 `P6DbbMinRescaleP6KT`）。
* consumer：(A) hgapJ 记号下（`c = r²`、`Tn = rescaleTime Tno`、`tK := Tn`）G1 槽类型逐字 + `hTnK`；
  (B) 同一阈值 `Q n := max (n+1) (ρ_p(tK n)²)⁻¹` 同时付 `hscaleK`（HNOT G3 `hscaleK_of_sepRhoPlus_P6HN`
  在 `σ := tK n` 处，即 (SEP-ρ⁺@t_n)）与 `hslabK`/(D2)（本文件，经连接行 `hlink`：K 帧 profile 天花板
  `c·ρ(tKo)⁻² ≤ ρ_p(tKo/c)⁻²`，= `p n` 与 `q` 的 linked 条款 + 重标度；example 前提，非合同）。
PROVED（无新 binder；example 的前提只是演示接线）。
-/

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- 反单调正半径 ⇒ 天花板：`t ≤ H` 处 `(ρ t²)⁻¹ ≤ (ρ H²)⁻¹ ≤ Q`（KSLABK `ceil_of_antitone_P6KS` 同式）。 -/
theorem ceilT_of_antitone_P6KT {ρ : ℝ → ℝ} (hρ : AntitoneOn ρ (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < ρ t) {H Q : ℝ} (hQ : (ρ H ^ 2)⁻¹ ≤ Q) {t : ℝ} (ht0 : 0 ≤ t)
    (htH : t ≤ H) : (ρ t ^ 2)⁻¹ ≤ Q := by
  have hH0 : 0 ≤ H := ht0.trans htH
  have hle : ρ H ≤ ρ t := hρ (mem_Ici.mpr ht0) (mem_Ici.mpr hH0) htH
  have hsq : ρ H ^ 2 ≤ ρ t ^ 2 := pow_le_pow_left₀ (hpos H hH0).le hle 2
  exact (inv_anti₀ (pow_pos (hpos H hH0) 2) hsq).trans hQ

/-- **点态截断天花板（event slabs，塔帧，`_P6KT`）**：supply + `Ctime ≤ Ctime₀` +
`∀ t ∈ [0, tK), (ρ t²)⁻¹ ≤ Q` ⇒ 每个 event slab 到 `min (time j.succ) tK` 的时间导数界。 -/
theorem eventSlabsDerivT_of_supply_P6KT {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀) (n : ℕ) {Q tK : ℝ}
    (hQ : ∀ t : ℝ, 0 ≤ t → t < tK → (ρ t ^ 2)⁻¹ ≤ Q) :
    ∀ j : Fin (F.tower.history n).eventCount,
      ((F.tower.history n).toHistory.event j).incoming.DerivativeBoundBefore Ctime₀ Q
        (min ((F.tower.history n).time j.succ) tK) := by
  intro j y t ht hR
  have h0 : 0 ≤ t := by
    have hz : (F.tower.history n).time 0 ≤ (F.tower.history n).time j.castSucc :=
      (F.tower.history n).time_strictMono.monotone (Fin.zero_le _)
    rw [(F.tower.history n).time_zero] at hz
    exact hz.trans ht.1.le
  have ht2 := lt_min_iff.mp ht.2
  refine (hTD.1 n j y t ⟨ht.1, ht2.1⟩ ((hQ t h0 ht2.2).trans_lt hR)).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (sq_nonneg _)

/-- **点态截断天花板（final slab，塔帧，`_P6KT`）**：同上，final slab 到 `min horizon tK`。 -/
theorem finalSlabDerivT_of_supply_P6KT {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀) (n : ℕ) {Q tK : ℝ}
    (hQ : ∀ t : ℝ, 0 ≤ t → t < tK → (ρ t ^ 2)⁻¹ ≤ Q)
    (hK : (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) <
      (F.tower.history n).horizon) :
    (((F.tower.history n).finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore
      Ctime₀ Q (min (F.tower.history n).horizon tK) := by
  intro y t ht hR
  have h0 : 0 ≤ t := by
    have hz : (F.tower.history n).time 0 ≤
        (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) :=
      (F.tower.history n).time_strictMono.monotone (Fin.zero_le _)
    rw [(F.tower.history n).time_zero] at hz
    exact hz.trans ht.1.le
  have ht2 := lt_min_iff.mp ht.2
  refine (hTD.2 n hK y t ⟨ht.1, ht2.1⟩ ((hQ t h0 ht2.2).trans_lt hR)).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (sq_nonneg _)

/-- **hslabKT（hgapJ 元组截断形，原尺度 `Ho n = F.tower.history (ind n)`，`_P6KT`）**：截断点 `tKo n`
处的天花板 `(ρ(tKo n)²)⁻¹ ≤ Qs n` + `ρ` 反单调正 ⇒ 截断形合取项。 -/
theorem hslabKT_of_supply_P6KT {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀)
    (hρ : AntitoneOn ρ (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < ρ t) (ind : ℕ → ℕ) (Qs tKo : ℕ → ℝ)
    (hQs : ∀ n, (ρ (tKo n) ^ 2)⁻¹ ≤ Qs n) :
    ∀ n (j : Fin (F.tower.history (ind n)).eventCount),
      ((F.tower.history (ind n)).toHistory.event j).incoming.DerivativeBoundBefore Ctime₀ (Qs n)
        (min ((F.tower.history (ind n)).time j.succ) (tKo n)) := fun n =>
  eventSlabsDerivT_of_supply_P6KT hTD hC (ind n) fun _ ht0 htK =>
    ceilT_of_antitone_P6KT hρ hpos (hQs n) ht0 htK.le

/-- **K 帧截断 (hslabK / D1)(D2)（`_P6KT`）**：原尺度截断点 `tKo n` 处天花板 `(ρ(tKo n)²)⁻¹ ≤ Qo n` ⇒
`K n = (Ho n).rescale_P6N (c n)` 上阈值 `c n · Qo n`、截断点 `tKo n / c n` 的 G1 槽形
（`NotKBodyT_P6KT` 的 `hslabK`、`FinalBodyT_P6KT` 的 (D1)（同形）与 (D2)）。 -/
theorem hkernelDtT_of_supply_P6KT {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀)
    (hρ : AntitoneOn ρ (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < ρ t) (ind : ℕ → ℕ) (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n) (Qo tKo : ℕ → ℝ) (hQo : ∀ n, (ρ (tKo n) ^ 2)⁻¹ ≤ Qo n) :
    let K : ℕ → RetainedCoreHistory.{u} := fun n =>
      (F.tower.history (ind n)).rescale_P6N (c n) (hc n)
    (∀ n (j : Fin (K n).eventCount),
      ((K n).toHistory.event j).incoming.DerivativeBoundBefore Ctime₀ (c n * Qo n)
        (min ((K n).time j.succ) (tKo n / c n))) ∧
      (∀ n (hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore
          Ctime₀ (c n * Qo n) (min (K n).horizon (tKo n / c n))) := by
  intro K
  have hQ : ∀ n, ∀ t : ℝ, 0 ≤ t → t < tKo n → (ρ t ^ 2)⁻¹ ≤ Qo n :=
    fun n _ ht0 htK => ceilT_of_antitone_P6KT hρ hpos (hQo n) ht0 htK.le
  refine ⟨fun n => ?_, fun n hfin => ?_⟩
  · exact (F.tower.history (ind n)).eventSlabsDerivT_rescale_P6KT (hc n)
      (eventSlabsDerivT_of_supply_P6KT hTD hC (ind n) (hQ n))
  · exact (F.tower.history (ind n)).derivativeBoundBefore_finalSlab_min_rescale_P6KT (hc n)
      (fun hK => finalSlabDerivT_of_supply_P6KT hTD hC (ind n) (hQ n) hK) hfin

/-! ## consumers -/

/-- consumer (A)：hgapJ 记号（`c = r²`、`K = rescale`、`Tn = rescaleTime Tno`），截断点 `tK := Tn`、
阈值 `Q n := c n · max ((n+1)/c n) (ρ(Tno n)²)⁻¹`（KSLABK 推荐阈值，天花板改在 `Tno`）：
G1 `NotKBodyT_P6KT` 的 `hslabK` 槽、`FinalBodyT_P6KT` 的 (D1)(D2) 槽类型逐字 + 连接行 `hTnK`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {Ctime : ℝ≥0} (hρ : AntitoneOn q.neckRadius (Ici 0))
    (hTD : TimeDerivativeSupply_C11E F q.neckRadius Ctime) (ind : ℕ → ℕ) (r : ℕ → ℝ)
    (hr : ∀ k, 0 < r k) (Tno : ∀ k, Icc (0 : ℝ) (F.tower.history (ind k)).toHistory.horizon) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    let c : ℕ → ℝ := fun k => r k ^ 2
    let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
    let Tn : ∀ k, Icc (0 : ℝ) (K k).toHistory.horizon := fun k =>
      (Ho k).rescaleTime_P6X (hc k) (Tno k)
    let Q : ℕ → ℝ := fun n => c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
    let tK : ℕ → ℝ := fun n => (Tn n : ℝ)
    (∀ n (j : Fin (K n).eventCount),
      ((K n).toHistory.event j).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time j.succ) (tK n))) ∧
      (∀ n (hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore
          Ctime (Q n) (min (K n).horizon (tK n))) ∧
      (∀ n, (Tn n : ℝ) ≤ tK n) := by
  intro Ho c hc K Tn Q tK
  obtain ⟨h1, h2⟩ := hkernelDtT_of_supply_P6KT hTD le_rfl hρ q.neckRadius_pos ind c hc
    (fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹) (fun n => (Tno n : ℝ))
    (fun _ => le_max_right _ _)
  exact ⟨h1, h2, fun _ => le_rfl⟩

/-- consumer (B)：**同一阈值** `Q n := max (n+1) (ρ_p(tK n)²)⁻¹`（`ρ_p = (p n).neckRadius`，K 帧，
`tK n := tKo n / c n`）同时付 kernel `hscaleK` 槽（HNOT G3 `hscaleK_of_sepRhoPlus_P6HN` 在 `σ := tK n`，
`hpast` = (SEP-ρ⁺@tK)）与截断 `hslabK` / (D2) 槽（本文件；`hlink` = K 帧 profile 天花板连接
`c·ρ_q(tKo)⁻² ≤ ρ_p(tKo/c)⁻²`，linked 条款 + 重标度给出；此处为 example 前提）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {Ctime : ℝ≥0} (hρ : AntitoneOn q.neckRadius (Ici 0))
    (hTD : TimeDerivativeSupply_C11E F q.neckRadius Ctime) (ind : ℕ → ℕ) (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n) (tKo : ℕ → ℝ) (htK0 : ∀ n, 0 ≤ tKo n) {p : ℕ → CutoffParameters}
    {T₀ : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount),
      T₀ n ≤ ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ →
      GeometricCutoffRecord ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory i (p n))
    (hanti : ∀ n, AntitoneOn (p n).neckRadius (Ici 0))
    (hlink : ∀ n, c n * (q.neckRadius (tKo n) ^ 2)⁻¹ ≤ ((p n).neckRadius (tKo n / c n) ^ 2)⁻¹)
    (hpast : ∀ (n : ℕ) i hi b,
      ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ ≤ tKo n / c n →
      ((n : ℝ) + 1) * max ((n : ℝ) + 1) ((p n).neckRadius (tKo n / c n) ^ 2)⁻¹ ≤
        ((recordsK n i hi).static b).neck.scale)
    (hΛδ : ∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount),
      T₀ n ≤ ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ →
      tKo n / c n < ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ →
      (p n).recenterConstant *
        (p n).delta (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ) ≤ 1 / 2)
    (hδ : ∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount),
      T₀ n ≤ ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ →
      tKo n / c n < ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ →
      (p n).delta (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ) ^ 4 *
        (2 * ((n : ℝ) + 1) * max 1 (((n : ℝ) + 1) * (p n).neckRadius 0 ^ 2)) ≤ 1) :
    let K : ℕ → RetainedCoreHistory.{u} := fun n =>
      (F.tower.history (ind n)).rescale_P6N (c n) (hc n)
    let tK : ℕ → ℝ := fun n => tKo n / c n
    let Q : ℕ → ℝ := fun n => max ((n : ℝ) + 1) ((p n).neckRadius (tK n) ^ 2)⁻¹
    (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore Ctime (Q n)
          (min ((K n).time j.succ) (tK n))) ∧
      (∀ n (hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore
          Ctime (Q n) (min (K n).horizon (tK n))) := by
  intro K tK Q
  have hQo : ∀ n, (q.neckRadius (tKo n) ^ 2)⁻¹ ≤ Q n / c n := fun n => by
    rw [le_div_iff₀ (hc n), mul_comm]
    exact (hlink n).trans (le_max_right _ _)
  obtain ⟨h1, h2⟩ := hkernelDtT_of_supply_P6KT hTD le_rfl hρ q.neckRadius_pos ind c hc
    (fun n => Q n / c n) tKo hQo
  have e : ∀ n, c n * (Q n / c n) = Q n := fun n => mul_div_cancel₀ _ (hc n).ne'
  refine ⟨fun n => hscaleK_of_sepRhoPlus_P6HN (recordsK n) (hanti n)
      (div_nonneg (htK0 n) (hc n).le)
      (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (hpast n) (hΛδ n) (hδ n),
    fun n j => ?_, fun n hfin => ?_⟩
  · have h := h1 n j
    rwa [e n] at h
  · have h := h2 n hfin
    rwa [e n] at h

end GC.LongTime.Ch11
