import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireFinalP6WR2

set_option autoImplicit false

/-!
# kernel 槽 hslabK / final (D1)(D2) ⇐ 先验 `TimeDerivativeSupply_C11E`（O-CH11-KSLABK G1，后缀 `_P6KS`）

设计文档 `P6-CORE-INDUCTION-DESIGN-20261008.md` §7 第三行："hslabK 由先验付 ⇒ 槽形不动"。
本文件 PROVED（无新 binder）：
* **天花板事实**：supply 在时刻 `t` 只对 `R > ρ(t)⁻²` 给 `|∂ₜR| ≤ Ctime·R²`；`ρ` 反单调 ⇒ `ρ(t)⁻²` 随 `t` 非减，故
  `∀ t ≤ horizon, (ρ t²)⁻¹ ≤ Q` ⟺ `Q ≥ (ρ(horizon)²)⁻¹`——天花板必须取在 history 的 `horizon`。
  取在求值时刻 `t_n < horizon` 的 `max(n+1, ρ(t_n)⁻²)` 盖不住 `t_n` 之后的 slab
  （槽是全 `Fin.last` / 到 `horizon`）。
* 塔帧（原尺度 `Ho n = F.tower.history (ind n)`，hgapJ 元组 HPB3 :639 / :917 的形）：
  `eventSlabsDerivative_of_supply_P6KS`（点态天花板）、
  `hslabK_of_supply_P6KS`（`Qs n ≥ ρ(horizon)⁻²` + antitone）、
  `finalSlabDerivative_of_supply_P6KS`（final slab 到 `horizon`）。
* K 帧（`K n = (Ho n).rescale_P6N (c n)`，hgapJF 元组 HPB3 :1192–1194 的形）：
  `hfinalDt_of_supply_P6KS` 给 (D1)(D2)，
  阈值 `Q n = c n · Qo n`（树内重标度：`eventSlabsDerivative_rescale_P6X3`、
  `derivativeBoundBefore_finalSlab_rescale_P6WR2`；`Ctime` 不变、阈值 ×c）。
* 推荐阈值：原尺度 `Qs n := max ((n+1)/c n) (ρ(horizon_n)²)⁻¹`（K 帧 `c·Qs = max (n+1) (c·ρ(horizon_n)⁻²)`）；
  同一 `Qs` 进 hscaleK ⇒ hscaleK = (SEP-ρ⁺) 在**天花板** `horizon_n` 处（HNOT owner，本车道不付）。
-/

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- 反单调正半径 ⇒ 天花板：`t ≤ H` 处 `(ρ t²)⁻¹ ≤ (ρ H²)⁻¹ ≤ Q`。 -/
theorem ceil_of_antitone_P6KS {ρ : ℝ → ℝ} (hρ : AntitoneOn ρ (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < ρ t) {H Q : ℝ} (hQ : (ρ H ^ 2)⁻¹ ≤ Q) {t : ℝ} (ht0 : 0 ≤ t)
    (htH : t ≤ H) : (ρ t ^ 2)⁻¹ ≤ Q := by
  have hH0 : 0 ≤ H := ht0.trans htH
  have hle : ρ H ≤ ρ t := hρ (mem_Ici.mpr ht0) (mem_Ici.mpr hH0) htH
  have hsq : ρ H ^ 2 ≤ ρ t ^ 2 := pow_le_pow_left₀ (hpos H hH0).le hle 2
  exact (inv_anti₀ (pow_pos (hpos H hH0) 2) hsq).trans hQ

/-- **点态天花板（event slabs，塔帧）**：supply + `Ctime ≤ Ctime₀` + `∀ t ∈ [0, horizon), (ρ t²)⁻¹ ≤ Q` ⇒
`(F.tower.history n).EventSlabsDerivative Ctime₀ Q (Fin.last …)`。 -/
theorem eventSlabsDerivative_of_supply_P6KS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀) (n : ℕ) {Q : ℝ}
    (hQ : ∀ t : ℝ, 0 ≤ t → t < (F.tower.history n).horizon → (ρ t ^ 2)⁻¹ ≤ Q) :
    (F.tower.history n).EventSlabsDerivative Ctime₀ Q
      (Fin.last (F.tower.history n).eventCount) := by
  intro j _ y t ht hR
  have h0 : 0 ≤ t := by
    have hz : (F.tower.history n).time 0 ≤ (F.tower.history n).time j.castSucc :=
      (F.tower.history n).time_strictMono.monotone (Fin.zero_le _)
    rw [(F.tower.history n).time_zero] at hz
    exact hz.trans ht.1.le
  have htH : t < (F.tower.history n).horizon :=
    ht.2.trans_le (((F.tower.history n).time_strictMono.monotone (Fin.le_last _)).trans
      (F.tower.history n).time_le_horizon)
  refine (hTD.1 n j y t ht ((hQ t h0 htH).trans_lt hR)).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (sq_nonneg _)

/-- **点态天花板（final slab，塔帧）**：同上，final slab 到 `horizon`（(D2) 的原尺度形）。 -/
theorem finalSlabDerivative_of_supply_P6KS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀) (n : ℕ) {Q : ℝ}
    (hQ : ∀ t : ℝ, 0 ≤ t → t < (F.tower.history n).horizon → (ρ t ^ 2)⁻¹ ≤ Q)
    (hK : (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) <
      (F.tower.history n).horizon) :
    (((F.tower.history n).finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore
      Ctime₀ Q (F.tower.history n).horizon := by
  intro y t ht hR
  have h0 : 0 ≤ t := by
    have hz : (F.tower.history n).time 0 ≤
        (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) :=
      (F.tower.history n).time_strictMono.monotone (Fin.zero_le _)
    rw [(F.tower.history n).time_zero] at hz
    exact hz.trans ht.1.le
  refine (hTD.2 n hK y t ht ((hQ t h0 ht.2).trans_lt hR)).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (sq_nonneg _)

/-- **hslabK（hgapJ 元组形，原尺度 `Ho n = F.tower.history (ind n)`）**：天花板 `(ρ(horizon_n)²)⁻¹ ≤ Qs n`
+ `ρ` 反单调正 ⇒ HPB3 :639 / :917 的合取项逐字。 -/
theorem hslabK_of_supply_P6KS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀)
    (hρ : AntitoneOn ρ (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < ρ t) (ind : ℕ → ℕ) (Qs : ℕ → ℝ)
    (hQs : ∀ n, (ρ (F.tower.history (ind n)).horizon ^ 2)⁻¹ ≤ Qs n) :
    ∀ n, (F.tower.history (ind n)).EventSlabsDerivative Ctime₀ (Qs n)
      (Fin.last (F.tower.history (ind n)).eventCount) := fun n =>
  eventSlabsDerivative_of_supply_P6KS hTD hC (ind n) fun _ ht0 htH =>
    ceil_of_antitone_P6KS hρ hpos (hQs n) ht0 htH.le

/-- **final (D1)(D2)（hgapJF 元组形，K 帧 `K n = (Ho n).rescale_P6N (c n)`）**：原尺度天花板
`(ρ(horizon_n)²)⁻¹ ≤ Qo n` ⇒ K 帧阈值 `c n · Qo n` 下的 (D1) event slabs 与 (D2) final slab
（HPB3 :1192–1194 逐字）。 -/
theorem hfinalDt_of_supply_P6KS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {Ctime Ctime₀ : ℝ≥0}
    (hTD : TimeDerivativeSupply_C11E F ρ Ctime) (hC : Ctime ≤ Ctime₀)
    (hρ : AntitoneOn ρ (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < ρ t) (ind : ℕ → ℕ) (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n) (Qo : ℕ → ℝ)
    (hQo : ∀ n, (ρ (F.tower.history (ind n)).horizon ^ 2)⁻¹ ≤ Qo n) :
    let K : ℕ → RetainedCoreHistory.{u} := fun n =>
      (F.tower.history (ind n)).rescale_P6N (c n) (hc n)
    (∀ n, (K n).EventSlabsDerivative Ctime₀ (c n * Qo n) (Fin.last (K n).eventCount)) ∧
      (∀ n (hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore
          Ctime₀ (c n * Qo n) (K n).horizon) := by
  intro K
  have hQ : ∀ n, ∀ t : ℝ, 0 ≤ t → t < (F.tower.history (ind n)).horizon →
      (ρ t ^ 2)⁻¹ ≤ Qo n := fun n _ ht0 htH => ceil_of_antitone_P6KS hρ hpos (hQo n) ht0 htH.le
  refine ⟨fun n => ?_, fun n hfin => ?_⟩
  · exact (F.tower.history (ind n)).eventSlabsDerivative_rescale_P6X3 (hc n)
      (eventSlabsDerivative_of_supply_P6KS hTD hC (ind n) (hQ n))
  · exact (F.tower.history (ind n)).derivativeBoundBefore_finalSlab_rescale_P6WR2 (hc n)
      (fun hK => finalSlabDerivative_of_supply_P6KS hTD hC (ind n) (hQ n) hK) hfin

/-! ## consumers（HPB3 合取项类型逐字） -/

/-- consumer：HPB3 :639 / :917（hgapJ / outer 元组，原尺度）的 hslabK 合取项，取推荐阈值
`Qs n := max ((n+1)/c n) (ρ(horizon_n)²)⁻¹`、`Ctime₀ := Ctime`、`ρ := q.neckRadius`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {Ctime : ℝ≥0} (hρ : AntitoneOn q.neckRadius (Ici 0))
    (hTD : TimeDerivativeSupply_C11E F q.neckRadius Ctime) (ind : ℕ → ℕ) (c : ℕ → ℝ) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    let Qs : ℕ → ℝ := fun n =>
      max (((n : ℝ) + 1) / c n) (q.neckRadius (Ho n).horizon ^ 2)⁻¹
    (∀ n, (Ho n).EventSlabsDerivative Ctime (Qs n) (Fin.last (Ho n).eventCount)) :=
  hslabK_of_supply_P6KS hTD le_rfl hρ q.neckRadius_pos ind _ fun _ => le_max_right _ _

/-- consumer：HPB3 :1192–1194（hgapJF 元组，K 帧）的 (D1)(D2) 合取项，K 帧阈值
`Q n := c n * max ((n+1)/c n) (ρ(horizon_n)²)⁻¹`（= `max (n+1) (c n · ρ(horizon_n)⁻²)`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {Ctime : ℝ≥0} (hρ : AntitoneOn q.neckRadius (Ici 0))
    (hTD : TimeDerivativeSupply_C11E F q.neckRadius Ctime) (ind : ℕ → ℕ) (r : ℕ → ℝ)
    (hr : ∀ k, 0 < r k) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    let c : ℕ → ℝ := fun k => r k ^ 2
    let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
    let Q : ℕ → ℝ := fun n =>
      c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Ho n).horizon ^ 2)⁻¹
    (∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) ∧
      (∀ n (hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore
          Ctime (Q n) (K n).horizon) :=
  hfinalDt_of_supply_P6KS hTD le_rfl hρ q.neckRadius_pos ind _ (fun k => pow_pos (hr k) 2) _
    fun _ => le_max_right _ _

end GC.LongTime.Ch11
