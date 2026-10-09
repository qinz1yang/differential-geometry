import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FootprintProducerP6PF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizeP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateCoreP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3

/-!
# F3 尺度分离 `hscaleSep`：由 record 的 `nominal_small` + ceiling + cutoff δ→0 拼出
# （S-CH11-SCALESEP G1 / G2 / G3，后缀 `_P6SS`）

HFOOT 遗留 F3（`hBCDE_of_localBCD_P6PF` 的第二个分析 binder `hscaleSep`，文本
build-logs/scratch/O-CH11-HFOOT/hscaleSep.txt）：selected family 上 eventually 有 record `Rc`，
`δ_j ≤ 1/2` 且 `Q_A · R_k < (1 − 4323 δ_j) · (Rc.neck j).scale`。

数学（一页）：设 `t = time (i k).succ = σ_k`，`d = pp.delta t`，`ρ = pp.neckRadius t`。
* record 侧：`nominal_small : r_j < d² ρ`、`scale_eq : scale_j = (r_j²)⁻¹`
  ⇒ `scale_j > (d⁴ ρ²)⁻¹`；`delta_le : δ_j ≤ d`。
* ceiling 侧：selected 点 `R_k ≤ (ρ̃(σ_k)²)⁻¹`，`ρ̃ = (q.rescale_P6N c_k).neckRadius`，**取在 record
  时刻 `σ_k`**。selection 输出的 `R n ≤ ρ(Tn n)⁻²` 是 `Tn` 处较弱版（`ρ(Tn) ≤ ρ(σ)`）；
  `ceiling_of_bad_P6HP`（取 `Tn := t`）能给 `σ` 处 ceiling，但前提是坏点谓词
  `¬∃ W η₁ C1₁ C2₁` + `hcan₁` 在 `(η₁, C1₁, C2₁)`，而 selected 点只有
  `¬ HasSpatialCanonicalTimeControl ε C1 C2 Ctime`。故这里对 Good 谓词直接重做：S5（`hcan`）+
  S11（`hder`）经 `canonical_rescale_P6X` / `derivative_rescale_P6X` 给出 `R > ρ̃⁻²` ⇒ Good，矛盾
  （`ceiling_of_not_good_P6SS`）。
* δ 侧：`q.delta → 0` 与 `c_k σ_k ≥ (k+1)/2`（clock `aSeed = Tn − 1`、`1 ≤ aSeed`、`k+1 ≤ c Tn`、
  `aSeed ≤ σ`）⇒ eventually `d ≤ δ₀ := 1/(8646 (Q_A + 1))`。
* 常数 `4323`：只经算术——`δ₀` 使 `4323 δ_j ≤ 1/2` 且 `Q_A d⁴ ≤ 1/8646`，故
  `Q_A R < Q_A d⁴ scale ≤ scale/8646 ≤ (1 − 4323 δ_j) scale`。`4323` 的几何来源（STAB3 G3 的 neck
  吸收常数）不在本文件用到，只在结论里逐字出现。

本文件：
* `record_scaleSep_P6SS`（PROVED，任意 record）：ceiling `R ≤ (ρ²)⁻¹` + `d ≤ δ₀` ⇒ 结论的 record 部分。
* `ceiling_of_not_good_P6SS`（PROVED）：`¬Good` + selector 形 `hcanonical` / `hderivative`
  ⇒ `R(y) ≤ (nr(σ)²)⁻¹`。
* `tendsto_delta_of_accuracyDecay_P6SS`（PROVED）：树内 S1 `AccuracyDecaySupply_C11S q.delta`
  ⇒ `hδq`。
* `lateRecords_of_S14_P6SS`（PROVED）：树内 S14 `LateLinkedRecordsSupply_C11E F q` ⇒ 原尺度 late
  records（P5L 形）。
* `hrec_of_lateRecords_P6SS`（G3 桥，PROVED）：原尺度 late records（P5L 形）⇒ 重标度形 `hrec`
  （`recordsKRescale_P6X3`）。
* **`hscaleSep_of_ceiling_P6SS`（G1a core，PROVISIONAL）**：结论 = `hscaleSep.txt` 逐字；binder
  `hδq`、`hrec`、`hceil`（σ 处 ceiling，前件 = `hscaleSep` 前缀逐字）。
* **`hscaleSep_of_records_P6SS`（G1b，PROVISIONAL）**：结论同上；binder `hcan`（S5）、`hder`（S11）、
  `hδq`、`hrec`，`hceil` 由 `ceiling_of_not_good_P6SS` 付。其中
  - `hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2`（与
    `canonicalLateCore_of_pureClass_P6X` 同形，**须在 Good 谓词同一 `(ε, C1, C2)`**；
    owner = surgery 构造 / P6OUTER·CX-OUTER2 的 hcan 链）；
  - `hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime`（S11，同上）；
  - `hδq : Tendsto q.delta atTop (𝓝 0)`（tower 的 δ(t) → 0；树内
    `exists_lateKdata_nominal_diag_CXKN` / `exists_lateKdata_of_P5L_P6LT` 同名 binder；
    owner = Perelman δ(r) 选择 / surgery 构造；树内 S1 `AccuracyDecaySupply_C11S q.delta` 给出它）；
  - `hrec`（late records，参数绑定 `q.rescale_P6N (c k)`）：由 G3 桥从原尺度 P5L 形 records
    （`p.delta = q.delta ∧ p.neckRadius = q.neckRadius`，owner = P5L 链）得到。
  `hcapWL` 的 late records binder（`hcapWL_of_records_P6HB` 的 `hrec`）里 `pp` 是任意的（只带
  `modelAccuracy` / `modelRadius` / `modelOrder`），**不带** `delta` / `neckRadius` 与 `q` 的绑定，
  所以不能直接当 `hrec`；`hBCDE` 的 record 只要求 `δ_j ≤ 1/2` 与尺度条件，不需要与 `hcapWL`
  同一 record。
* **`hfootE_of_localBCD_records_P6SS`（G2 consumer）**：`hlocBCD`（binder 形，文本 `hlocBCD.txt`
  逐字）+ 树内四个具名供给 `hcan`（S5）/ `hder`（S11）/ `hS1`（S1）/ `hS14`（S14）⇒ `hfootE`
  （`hfootE.txt` 逐字），经
  `hscaleSep_of_records_P6SS`、`hBCDE_of_localBCD_P6PF` 与 `hfootE_of_terminalBCD_P6PF`。
陈述由 build-logs/scratch/S-CH11-SCALESEP/gen.py 从 `hscaleSep.txt` / `hlocBCD.txt` /
`hfootE.txt` 逐字生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

/-- **S1 ⇒ `hδq`（PROVED）**：树内 S1 `AccuracyDecaySupply_C11S q.delta`（antitone + decay）加
`delta_pos` 给出 `Tendsto q.delta atTop (𝓝 0)`，即本文件的 binder `hδq`。 -/
theorem tendsto_delta_of_accuracyDecay_P6SS (q : CutoffParameters)
    (h : GC.LongTime.Ch11.AccuracyDecaySupply_C11S q.delta) : Tendsto q.delta atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨B, hB⟩ := h.2 ε hε
  refine ⟨max B 0 + 1, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith [le_max_right B 0]
  have hBt : B < t := by linarith [le_max_left B 0]
  rw [Real.dist_eq, sub_zero, abs_of_pos (q.delta_pos t ht0)]
  exact hB t hBt

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

/-- **record 侧尺度分离（任意 record，PROVED）**：ceiling `R ≤ (ρ²)⁻¹`（`ρ = pp.neckRadius t`）与
`pp.delta t ≤ 1/(8646 (Q_A + 1))`（`t = H.time i.succ`）⇒ `δ_j ≤ 1/2` 且
`Q_A · R < (1 − 4323 δ_j) · scale_j`。用 `nominal_small`（`r_j < d² ρ`）、`scale_eq`（`scale = (r²)⁻¹`）
与 `delta_le`（`δ_j ≤ d`）；严格性来自 `nominal_small` 的严格不等号（不需要 `R > 0`）。 -/
theorem record_scaleSep_P6SS (Rc : GeometricCutoffRecord H i pp) {QA R : ℝ} (hQA : 0 < QA)
    (hceil : R ≤ (pp.neckRadius (H.time i.succ) ^ 2)⁻¹)
    (hδ : pp.delta (H.time i.succ) ≤ 1 / (8646 * (QA + 1))) :
    (∀ j, Rc.delta j ≤ 1 / 2) ∧ ∀ j, QA * R < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale := by
  have ht : 0 ≤ H.time i.succ := H.time_nonneg i.succ
  have hd0 : 0 < pp.delta (H.time i.succ) := pp.delta_pos _ ht
  have hρ0 : 0 < pp.neckRadius (H.time i.succ) := pp.neckRadius_pos _ ht
  have hq0 : 0 < 8646 * (QA + 1) := by positivity
  have hdq : pp.delta (H.time i.succ) * (8646 * (QA + 1)) ≤ 1 := (le_div_iff₀ hq0).mp hδ
  have hd1 : pp.delta (H.time i.succ) ≤ 1 / 8646 := by
    nlinarith [mul_pos hd0 hQA]
  have hd4 : pp.delta (H.time i.succ) ^ 4 ≤ pp.delta (H.time i.succ) :=
    pow_le_of_le_one hd0.le (by linarith) (by norm_num)
  have hQd : QA * pp.delta (H.time i.succ) ^ 4 ≤ 1 / 8646 := by
    nlinarith [mul_le_mul_of_nonneg_left hd4 hQA.le, mul_pos hd0 hQA]
  refine ⟨fun j => (Rc.delta_le j).trans (hd1.trans (by norm_num)), fun j => ?_⟩
  have hδj : Rc.delta j ≤ pp.delta (H.time i.succ) := Rc.delta_le j
  have hn := Rc.nominal_small ⟨j⟩
  have hnpos := Rc.nominal_pos ⟨j⟩
  have hsc := Rc.scale_eq j
  have hρ2 : 0 < pp.neckRadius (H.time i.succ) ^ 2 := pow_pos hρ0 2
  have hd4pos : 0 < pp.delta (H.time i.succ) ^ 4 := pow_pos hd0 4
  have hr2 : Rc.nominalRadius ⟨j⟩ ^ 2 <
      pp.delta (H.time i.succ) ^ 4 * pp.neckRadius (H.time i.succ) ^ 2 :=
    calc Rc.nominalRadius ⟨j⟩ ^ 2
        < (pp.delta (H.time i.succ) ^ 2 * pp.neckRadius (H.time i.succ)) ^ 2 :=
          pow_lt_pow_left₀ hn hnpos.le two_ne_zero
      _ = pp.delta (H.time i.succ) ^ 4 * pp.neckRadius (H.time i.succ) ^ 2 := by ring
  have hS1 : (pp.delta (H.time i.succ) ^ 4 * pp.neckRadius (H.time i.succ) ^ 2)⁻¹ <
      (Rc.neck j).scale := by
    rw [hsc]
    exact inv_strictAnti₀ (pow_pos hnpos 2) hr2
  have hS0 : 0 < (Rc.neck j).scale :=
    lt_trans (inv_pos.mpr (mul_pos hd4pos hρ2)) hS1
  have hRS : R < pp.delta (H.time i.succ) ^ 4 * (Rc.neck j).scale :=
    calc R ≤ (pp.neckRadius (H.time i.succ) ^ 2)⁻¹ := hceil
      _ = pp.delta (H.time i.succ) ^ 4 *
          (pp.delta (H.time i.succ) ^ 4 * pp.neckRadius (H.time i.succ) ^ 2)⁻¹ := by
        rw [mul_inv, mul_inv_cancel_left₀ hd4pos.ne']
      _ < pp.delta (H.time i.succ) ^ 4 * (Rc.neck j).scale :=
        mul_lt_mul_of_pos_left hS1 hd4pos
  have hδ' : Rc.delta j ≤ 1 / 8646 := hδj.trans hd1
  calc QA * R < QA * (pp.delta (H.time i.succ) ^ 4 * (Rc.neck j).scale) :=
        mul_lt_mul_of_pos_left hRS hQA
    _ = (QA * pp.delta (H.time i.succ) ^ 4) * (Rc.neck j).scale := by ring
    _ ≤ (1 / 8646) * (Rc.neck j).scale := mul_le_mul_of_nonneg_right hQd hS0.le
    _ ≤ (1 - 4323 * Rc.delta j) * (Rc.neck j).scale :=
        mul_le_mul_of_nonneg_right (by linarith) hS0.le

end GeometricCutoffRecord

namespace ObservedHistory

/-- **ceiling 在 σ 处（PROVED）**：selector 的 `hcanonical` / `hderivative` 形供给 + `¬Good` ⇒
`R(σ, y) ≤ (nr(σ)²)⁻¹`（`R > nr⁻²` ⇒ spatial witness 与 time bound 都有 ⇒ Good，矛盾）。 -/
theorem ceiling_of_not_good_P6SS (H : ObservedHistory.{u}) {nr : ℝ → ℝ} {ε C1 C2 : ℝ}
    {Ctime : ℝ≥0}
    (hcan : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      (nr v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ε C1 C2 z,
        W.capTubeHasNeckChart ε)
    (hder : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      (nr v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt (H.stageMetric (H.activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v) z ^ 2)
    {σ : Icc (0 : ℝ) H.horizon} {y : (H.stageAt σ).Carrier}
    (hsel : ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y) :
    metricScalarAt (H.stageMetric (H.activeStage σ) σ) y ≤ (nr σ ^ 2)⁻¹ := by
  by_contra hlt
  exact hsel ⟨hcan σ y (lt_of_not_ge hlt), fun h1 h2 => hder σ y h1 h2 (lt_of_not_ge hlt)⟩

/-- **S14 ⇒ 原尺度 late records（PROVED）**：树内 S14 `LateLinkedRecordsSupply_C11E F q` 在
`(D, ζ, m) = (0, 1, 0)` 处只取 records 部分（`p.delta = q.delta ∧ p.neckRadius = q.neckRadius`）。 -/
theorem lateRecords_of_S14_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (h : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q) :
    ∃ T : ℝ, ∀ n : ℕ, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧
      Nonempty (∀ i : Fin (F.tower.history n).eventCount,
        T ≤ (F.tower.history n).time i.succ →
        GeometricCutoffRecord (F.tower.history n).toHistory i p) := by
  obtain ⟨T, hT⟩ := h 0 1 0 one_pos
  refine ⟨T, fun n => ?_⟩
  obtain ⟨p, hd, hn, -, -, -, -, -, records, -⟩ := hT n
  exact ⟨p, hd, hn, ⟨records⟩⟩

/-- **`hrec` ⇐ 原尺度 late records（P5L 形，G3 桥，PROVED）**：`∃ T, ∀ n, ∃ p, p.delta = q.delta ∧
p.neckRadius = q.neckRadius ∧ late records`（`hP5L` 的 records 部分，去掉 model 数据与 canonical window）
经 `recordsKRescale_P6X3`（`p ↦ p.rescale_P6N c`，late 量词 `max 1 (T/c)`）给出重标度形 `hrec`。
重标度 late 量词多要 `1 ≤ time`（`hrec` 的前件 `∀ k, 1 ≤ time`），`c_k time → ∞` ⇒ eventually
`T ≤ c_k time`。 -/
theorem hrec_of_lateRecords_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (hrecO : ∃ T : ℝ, ∀ n : ℕ, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧
      Nonempty (∀ i : Fin (F.tower.history n).eventCount,
        T ≤ (F.tower.history n).time i.succ →
        GeometricCutoffRecord (F.tower.history n).toHistory i p)) :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, 1 ≤ (Kh k).time (i k).succ) →
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ pp : CutoffParameters,
          pp.delta = (q.rescale_P6N (c k) (hc k)).delta ∧
          pp.neckRadius = (q.rescale_P6N (c k) (hc k)).neckRadius ∧
          Nonempty (GeometricCutoffRecord (Kh k) (i k) pp) := by
  obtain ⟨T, hT⟩ := hrecO
  intro ind c hc Kh i hone hlate
  filter_upwards [hlate.eventually_ge_atTop T] with k hk
  obtain ⟨p, hpd, hpn, ⟨records⟩⟩ := hT (ind k)
  refine ⟨p.rescale_P6N (c k) (hc k), ?_, ?_, ⟨?_⟩⟩
  · funext t
    change p.delta (c k * t) = q.delta (c k * t)
    rw [hpd]
  · funext t
    change p.neckRadius (c k * t) / Real.sqrt (c k) = q.neckRadius (c k * t) / Real.sqrt (c k)
    rw [hpn]
  · refine (F.tower.history (ind k)).recordsKRescale_P6X3 (hc k) records (i k)
      (max_le (hone k) ?_)
    rw [div_le_iff₀ (hc k), mul_comm]
    exact hk

/-- **F3 `hscaleSep` 的 core（G1a，PROVISIONAL）**：结论 = `hscaleSep.txt` 逐字。把 ceiling 作为 binder
`hceil`（selected family 上 `R_k ≤ (ρ̃(σ_k)²)⁻¹`，`ρ̃ = (q.rescale_P6N c_k).neckRadius`；
前件 = `hscaleSep` 的前缀逐字）：任何给出 σ 处 ceiling 的路线都可喂入（`hcan` / `hder` 路线见
`hscaleSep_of_records_P6SS`）。
其余 binder：`hδq`（`q.delta → 0`）、`hrec`（late records，参数绑定 `q.rescale_P6N (c k)`）。
取 `δ₀ := 1/(8646 (Q_A + 1))`，`pp`/`Rc` 取自 `hrec`。 -/
theorem hscaleSep_of_ceiling_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {q : CutoffParameters}
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (hrec : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, 1 ≤ (Kh k).time (i k).succ) →
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ pp : CutoffParameters,
          pp.delta = (q.rescale_P6N (c k) (hc k)).delta ∧
          pp.neckRadius = (q.rescale_P6N (c k) (hc k)).neckRadius ∧
          Nonempty (GeometricCutoffRecord (Kh k) (i k) pp))
    (hceil :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ k, R k ≤ (((q.rescale_P6N (c k) (hc k)).neckRadius (σ k)) ^ 2)⁻¹) :
      ∀ QA : ℝ, 0 < QA →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ j, Rc.delta j ≤ 1 / 2) ∧
          ∀ j, QA * R k < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale := by
  intro QA hQA ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos
    hRr hL hsel hgood hwin hwin' hroom hradii i hi
  have hcs : ∀ k : ℕ, ((k : ℝ) + 1) / 2 ≤ c k * (Kh k).time (i k).succ := fun k => by
    rw [← hi k]
    have hclk := hclock k
    have hTck := hTc k
    have hask : (aSeed k : ℝ) ≤ σ k := Subtype.coe_le_coe.mpr (has k)
    have h1k := h1 k
    have hck := hc k
    have hT2 : (Tn k : ℝ) ≤ 2 * (σ k : ℝ) := by
      rw [one_pow] at hclk
      linarith
    have := mul_le_mul_of_nonneg_left hT2 hck.le
    linarith
  have hT : Tendsto (fun k : ℕ => c k * (Kh k).time (i k).succ) atTop atTop :=
    tendsto_atTop_mono hcs
      ((tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_div_const two_pos)
  have hδpos : (0 : ℝ) < 1 / (8646 * (QA + 1)) := by positivity
  have hδev : ∀ᶠ k in atTop, q.delta (c k * (Kh k).time (i k).succ) ≤ 1 / (8646 * (QA + 1)) :=
    hT.eventually (hδq.eventually (ge_mem_nhds hδpos))
  have hone : ∀ k, 1 ≤ (Kh k).time (i k).succ := fun k => by
    rw [← hi k]
    exact (h1 k).trans (Subtype.coe_le_coe.mpr (has k))
  filter_upwards [hrec ind c hc i hone hT, hδev] with k hk hδk
  obtain ⟨pp, hpd, hpn, ⟨Rc⟩⟩ := hk
  refine ⟨pp, Rc, ?_⟩
  have hRk : R k ≤ (pp.neckRadius ((Kh k).time (i k).succ) ^ 2)⁻¹ := by
    rw [hpn, ← hi k]
    exact hceil ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos
      hRr hL hsel hgood hwin hwin' hroom hradii i hi k
  have hδk' : pp.delta ((Kh k).time (i k).succ) ≤ 1 / (8646 * (QA + 1)) := by
    rw [hpd]
    exact hδk
  exact Rc.record_scaleSep_P6SS hQA hRk hδk'

/-- **F3 `hscaleSep` 的 producer（G1b，PROVISIONAL）**：结论 = `hscaleSep.txt` 逐字。ceiling 由 S5 `hcan`
+ S11 `hder`（与 `canonicalLateCore_of_pureClass_P6X` 同形，**取在 Good 谓词同一
`(ε, C1, C2, Ctime)`**）经 `canonical_rescale_P6X` / `derivative_rescale_P6X` /
`ceiling_of_not_good_P6SS` 给出，喂 `hscaleSep_of_ceiling_P6SS`。若最终链只有 `hcan₁` 在
`(ηf, Cf, Cf)`（≠ Good 的 `(ε, C1, C2)`；`(η, C1, C2)` 间 witness 的单调搬运树内只对 neck 分支
有，见 `fineGood_implies_fineMarginGood_P6ST4`），请直接用 `hscaleSep_of_ceiling_P6SS`。 -/
theorem hscaleSep_of_records_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {q : CutoffParameters}
    (hcan : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (hrec : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, 1 ≤ (Kh k).time (i k).succ) →
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ pp : CutoffParameters,
          pp.delta = (q.rescale_P6N (c k) (hc k)).delta ∧
          pp.neckRadius = (q.rescale_P6N (c k) (hc k)).neckRadius ∧
          Nonempty (GeometricCutoffRecord (Kh k) (i k) pp)) :
      ∀ QA : ℝ, 0 < QA →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ j, Rc.delta j ≤ 1 / 2) ∧
          ∀ j, QA * R k < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale :=
  hscaleSep_of_ceiling_P6SS hδq hrec (by
    intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos
      hRr hL hsel hgood hwin hwin' hroom hradii i hi k
    have h := (Kh k).ceiling_of_not_good_P6SS
      (nr := (q.rescale_P6N (c k) (hc k)).neckRadius)
      ((F.tower.history (ind k)).canonical_rescale_P6X (hc k) (hcan (ind k)))
      ((F.tower.history (ind k)).derivative_rescale_P6X (hc k)
        (fun v z hlo hhi hR =>
          GC.LongTime.Ch11.stageDerivative_of_timeDerivativeSupply_P6X hder (ind k) v z hlo hhi hR))
      (hsel k)
    rw [hRdef k]
    exact h)

/-- **G2 consumer（PROVISIONAL）**：F2 `hlocBCD`（BCDT 的 binder 形，`hlocBCD.txt` 逐字）+ 树内具名
供给 S5 `hcan`、S11 `hder`、S1 `hS1`、S14 `hS14`（F3 的全部输入）⇒ `hfootE`（`hfootE.txt` 逐字）。
`hBCDE_of_localBCD_P6PF` 合成 `hBCDE`（F2 ∧ F3），再喂 `hfootE_of_terminalBCD_P6PF`。 -/
theorem hfootE_of_localBCD_records_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ}
    {q : CutoffParameters}
    (hε0 : 0 < ε) (hε : ε < 1 / 11) (hC1f : 1 ≤ C1f) (hC2f : 1 ≤ C2f) (hm0 : 0 < m)
    (hm1 : m ≤ 1 / 2) (hkk : max 2 ⌈ε⁻¹⌉₊ ≤ kk)
    (hlocBCD :
      ∀ A : ℝ, 0 < A → ∃ QA : ℝ, 0 < QA ∧
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ∀ hcross : ((Kh k).event (i k)).RegularCrossing p' q,
          ∀ z ∈ riemannianBallOf ((Kh k).event (i k)).terminal.metric
              ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩ (A / Real.sqrt (R k)),
            metricScalarAt ((Kh k).event (i k)).terminal.metric z ≤ QA * R k)
    (hcan : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hS1 : GC.LongTime.Ch11.AccuracyDecaySupply_C11S q.delta)
    (hS14 : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q) :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          Nonempty (((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk) :=
  hfootE_of_terminalBCD_P6PF hε0 hε hC1f hC2f hm0 hm1 hkk
    (hBCDE_of_localBCD_P6PF hlocBCD (hscaleSep_of_records_P6SS hcan hder
      (tendsto_delta_of_accuracyDecay_P6SS q hS1)
      (hrec_of_lateRecords_P6SS (lateRecords_of_S14_P6SS hS14))))

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
