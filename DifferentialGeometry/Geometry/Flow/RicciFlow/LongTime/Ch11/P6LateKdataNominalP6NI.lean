import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateSupplyAntiP6M3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepNeckP6CD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P5LNominalSupplyP6NI

/-!
# K 数据供给端的 nominal 识别合取（S-CH11-NOMID G1，后缀 `_P6NI`）

P6COND G3 的 `hnomId`（`hdistC_of_native_P6CD`：late `recordsK` 与 native `d.native.records` 的
`nominalRadius` 逐 tube 相同）BLOCKED 在 K 数据供给端：`exists_lateKdata_of_P5L_antitone_P6M3` 的
`recordsK` 是 `hP5L` 里的存在 record，来源不透明。lead R-C11-8 裁定：`recordsK` 取 native records 的
late restriction 是正确 repair，且若两套 records 的 `CutoffParameters` 不同（P5L 的 `p n` 有
`modelRadius → ∞`，native `params` 固定），必须**证** reparameterization 保留实际 neck / window。本文件：
* `reparam_refl_P6NI` / `lateRestriction_reparam_P6NI`：late restriction（同参数）⇒ reparameterization
  合取全 `rfl`（lead 点名的正确 repair 的退化情形）；
* `exists_lateKdata_of_P5L_antitone_nominal_P6NI`：原定理（antitone 版）的**重证副本**，`hP5L` 的
  `∃ records` 多一个 **reparameterization 合取**（`nominalRadius / delta / order / neck`、static neck
  scale、cap 嵌入同参考 record `recs n i`；inline 非具名 Prop；`recs` = 参数 `q` 的参考 records 族——P5L 供给里
  就是被换窗口的底 record，供给侧证明见 `P5LNominalSupplyP6NI`），结论 = 原六项 ∧ `(p n).delta = q.delta`、
  `(p n).recenterConstant = q.recenterConstant`（(DLT) 的来源）∧ 同一 reparameterization（对 `recordsK`）；
* `hnomId_of_ref_P6NI`：参考族 `recs` 传递到 native `d.native.records`（取 `q := d.native.params`、
  `recs := d.native.records` 时 `rfl`）；
* consumer `hdistC_of_P5L_nominal_P6NI`：`hdistC_of_native_P6CD` 的 K 层 binder
  （`recordsK hcanK hacc hrad hord hδK hnomId`）全由 `hP5L`（含 nominal 合取）供给，余下输入逐字。
* 文件末 `example`：astra 链的 P5L 供给 nominal 追踪版（`P5LNominalSupplyP6NI`，G1b）⇒ 本文件的
  K 数据定理的 `hP5L` binder（`K n := F.tower.history n`、`q`、`recs := records`）——整条供给链闭合。
由 build-logs/scratch/S-CH11-NOMID/mk_a.py 生成（证明体取自 `P6LateSupplyAntiP6M3`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- **P5L 形（带 nominal 合取）⇒ late 主形 (a) 组 ∧ nominal 识别（`_P6NI`）**：`hP5L` 的
`∃ records` 多合取 `nominalRadius = (recs n i).nominalRadius`；结论 = 原定理六项 ∧ 共同 `δ / Λ` ∧
`recordsK` 的 nominal 识别。 -/
theorem exists_lateKdata_of_P5L_antitone_nominal_P6NI {K : ℕ → RetainedCoreHistory.{u}}
    {q : CutoffParameters}
    (Q : ℕ → ℝ)
    (recs : ∀ n (i : Fin (K n).eventCount), GeometricCutoffRecord (K n).toHistory i q)
    (hP5L : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T : ℝ, ∀ n, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧
      m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (K n).eventCount, T ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) ∧
      ∀ i hi, (records i hi).nominalRadius =
          (recs n i).nominalRadius ∧
        (records i hi).delta =
          (recs n i).delta ∧
        (records i hi).order =
          (recs n i).order ∧
        (∀ α, HEq ((records i hi).neck α) ((recs n i).neck α)) ∧
        (∀ b, ((records i hi).static b).neck.scale =
          ((recs n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records i hi).static b).inclusion
              (((records i hi).static b).witness.cap z) =
            ((recs n i).static b).inclusion
              (((recs n i).static b).witness.cap z))
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) :
    ∃ (T₀ : ℕ → ℝ) (p : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)),
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
      (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
      (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        q.delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (p n).delta = q.delta) ∧
      (∀ n : ℕ, (p n).recenterConstant = q.recenterConstant) ∧
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ),
        (recordsK n i hi).nominalRadius =
          (recs n i).nominalRadius ∧
        (recordsK n i hi).delta =
          (recs n i).delta ∧
        (recordsK n i hi).order =
          (recs n i).order ∧
        (∀ α, HEq ((recordsK n i hi).neck α) ((recs n i).neck α)) ∧
        (∀ b, ((recordsK n i hi).static b).neck.scale =
          ((recs n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((recordsK n i hi).static b).inclusion
              (((recordsK n i hi).static b).witness.cap z) =
            ((recs n i).static b).inclusion
              (((recs n i).static b).witness.cap z)) := by
  have h1 : ∀ n : ℕ, ∃ T : ℝ, ∃ p : CutoffParameters, p.delta = q.delta ∧
      p.neckRadius = q.neckRadius ∧ p.recenterConstant = q.recenterConstant ∧
      (n : ℝ) + 1 ≤ p.modelRadius ∧ p.modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧
      n + 2 ≤ p.modelOrder ∧
      ∃ records : ∀ i : Fin (K n).eventCount, T ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) ∧
      ∀ i hi, (records i hi).nominalRadius =
          (recs n i).nominalRadius ∧
        (records i hi).delta =
          (recs n i).delta ∧
        (records i hi).order =
          (recs n i).order ∧
        (∀ α, HEq ((records i hi).neck α) ((recs n i).neck α)) ∧
        (∀ b, ((records i hi).static b).neck.scale =
          ((recs n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records i hi).static b).inclusion
              (((records i hi).static b).witness.cap z) =
            ((recs n i).static b).inclusion
              (((recs n i).static b).witness.cap z) := by
    intro n
    have hζ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨T, hT⟩ := hP5L ((n : ℝ) + 1) (1 / ((n : ℝ) + 1)) (n + 2) hζ
    obtain ⟨p, hpδ, hpρ, -, hprc, hprad, hpacc, hpord, records, hlink, hrp⟩ := hT n
    exact ⟨T, p, hpδ, hpρ, hprc, hprad, hpacc, hpord, records, hlink, hrp⟩
  choose T₁ p hpδ hpρ hprc hprad hpacc hpord records hlink hrp using h1
  have hrc : 0 < q.recenterConstant := by linarith [q.recenterConstant_ge_four]
  have hrc' : q.recenterConstant ≠ 0 := hrc.ne'
  have h2 : ∀ n : ℕ, ∃ T : ℝ, ∀ s ≥ T,
      q.delta s ≤ min (1 / ((n : ℝ) + 1)) (1 / (2 * q.recenterConstant)) := by
    intro n
    have hpos : (0 : ℝ) < min (1 / ((n : ℝ) + 1)) (1 / (2 * q.recenterConstant)) :=
      lt_min (by positivity) (by positivity)
    exact Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hpos))
  choose Tδ hTδ using h2
  have hcpos : ∀ n : ℕ, 0 < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := fun n =>
    mul_pos (by positivity) (lt_of_lt_of_le (by positivity) (le_max_left _ _))
  have hρ₁ : 0 < q.neckRadius 0 := q.neckRadius_pos 0 le_rfl
  have h3 : ∀ n : ℕ, ∃ T : ℝ, ∀ s ≥ T,
      q.delta s ≤ 1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)) * q.neckRadius 0) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)) * q.neckRadius 0) :=
      div_pos one_pos (mul_pos (mul_pos two_pos (hcpos n)) hρ₁)
    exact Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hpos))
  choose Tρ hTρ using h3
  have hle1 : ∀ n s, max (T₁ n) (max (Tδ n) (Tρ n)) ≤ s → T₁ n ≤ s := fun n s h =>
    (le_max_left _ _).trans h
  have hle2 : ∀ n s, max (T₁ n) (max (Tδ n) (Tρ n)) ≤ s → Tδ n ≤ s := fun n s h =>
    ((le_max_left _ _).trans (le_max_right _ _)).trans h
  have hle3 : ∀ n s, max (T₁ n) (max (Tδ n) (Tρ n)) ≤ s → Tρ n ≤ s := fun n s h =>
    ((le_max_right _ _).trans (le_max_right _ _)).trans h
  refine ⟨fun n => max (T₁ n) (max (Tδ n) (Tρ n)), p,
    fun n i hi => records n i (hle1 n _ hi),
    fun n i hi b => GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _
      (hlink n i (hle1 n _ hi) b), hpacc, hprad, hpord, ?_, ?_, hpδ, hprc,
    fun n i hi => hrp n i (hle1 n _ hi)⟩
  · intro n i hi b
    have hδs := hTδ n _ (hle2 n _ hi)
    have hρs := hTρ n _ (hle3 n _ hi)
    have hc1 : 1 ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have h2 : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
      nlinarith
    have hΛδ : (p n).recenterConstant * (1 / (2 * q.recenterConstant)) ≤ 1 / 2 :=
      le_of_eq (by rw [hprc n]; field_simp)
    have ht0 : 0 ≤ (K n).time i.succ := (K n).toHistory.time_nonneg i.succ
    have hdel1 : q.delta ((K n).time i.succ) < 1 := q.delta_lt_one _ ht0
    have hdel0 : 0 < q.delta ((K n).time i.succ) := q.delta_pos _ ht0
    have hρle : q.neckRadius ((K n).time i.succ) ≤ q.neckRadius 0 :=
      hρa (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0) ht0
    have hδρ : q.delta ((K n).time i.succ) ^ 2 * q.neckRadius 0 ≤
        1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n))) := by
      have hc := hcpos n
      have h1 : q.delta ((K n).time i.succ) * q.neckRadius 0 ≤
          1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n))) := by
        have h2 := (le_div_iff₀ (by positivity)).1 hρs
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have h3 : q.delta ((K n).time i.succ) ^ 2 * q.neckRadius 0 ≤
          q.delta ((K n).time i.succ) * q.neckRadius 0 := by
        have : q.delta ((K n).time i.succ) ^ 2 ≤ q.delta ((K n).time i.succ) := by nlinarith
        exact mul_le_mul_of_nonneg_right this hρ₁.le
      exact h3.trans h1
    have hΛδ' : (p n).recenterConstant * q.delta ((K n).time i.succ) ≤ 1 / 2 := by
      rw [hprc n]
      have h1 : q.delta ((K n).time i.succ) ≤ 1 / (2 * q.recenterConstant) :=
        hδs.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    have hlt := inv_two_mul_sq_lt_static_scale_record_delta_P6M3 (records n i (hle1 n _ hi))
      (δ₀ := q.delta ((K n).time i.succ)) (ρ₁ := q.neckRadius 0)
      (ρ₀ := 1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)))) hΛδ'
      (by rw [hpδ n]) (by rw [hpρ n]; exact hρle) hδρ b
    have heq : (2 * (1 / (2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)))) ^ 2)⁻¹ =
        2 * (((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)) ^ 2 := by
      have := (hcpos n).ne'
      field_simp
    rw [heq] at hlt
    change ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((records n i (hle1 n _ hi)).static b).neck.scale
    nlinarith
  · intro n i hi
    exact (hTδ n _ (hle2 n _ hi)).trans (min_le_left _ _)

end RetainedCoreHistory

/-- **late restriction（同参数）的退化情形**：任一 record 是自身的 reparameterization——全 `rfl`。
`recordsK := N.records` 的 late restriction（`lateRecords_of_pre841_C11G`）时 reparameterization 合取
即此。参数不同（P5L 的 `p n`）时合取由供给侧证（`P5LNominalSupplyP6NI`）。 -/
theorem reparam_refl_P6NI {H : ObservedHistory.{u}} {i : Fin H.eventCount} {q : CutoffParameters}
    (R : GeometricCutoffRecord H i q) :
    R.nominalRadius =
      R.nominalRadius ∧
    R.delta =
      R.delta ∧
    R.order =
      R.order ∧
    (∀ α, HEq (R.neck α) (R.neck α)) ∧
    (∀ b, (R.static b).neck.scale =
      (R.static b).neck.scale) ∧
    ∀ (b) (z : ThreeBall),
      (R.static b).inclusion
          ((R.static b).witness.cap z) =
        (R.static b).inclusion
          ((R.static b).witness.cap z) :=
  ⟨rfl, rfl, rfl, fun _ => HEq.rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- late restriction 版：`N.records` 作 `recordsK`（`T₀` 任意）满足 reparameterization 合取（对自身）。 -/
example {Hs : ℕ → ObservedHistory.{u}} (N : GC.LongTime.Ch11.Pre841NativeData_C11K Hs)
    (T₀ : ℕ → ℝ) :
    ∀ n (i : Fin (Hs n).eventCount) (_ : T₀ n ≤ (Hs n).time i.succ),
      (N.records n i).nominalRadius =
          (N.records n i).nominalRadius ∧
        (N.records n i).delta =
          (N.records n i).delta ∧
        (N.records n i).order =
          (N.records n i).order ∧
        (∀ α, HEq ((N.records n i).neck α) ((N.records n i).neck α)) ∧
        (∀ b, ((N.records n i).static b).neck.scale =
          ((N.records n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((N.records n i).static b).inclusion
              (((N.records n i).static b).witness.cap z) =
            ((N.records n i).static b).inclusion
              (((N.records n i).static b).witness.cap z) :=
  fun n i _ => reparam_refl_P6NI (N.records n i)

/-- **neck 识别的传递（`_P6NI`）**：late `recordsK` 的 nominal 半径等于参考族 `recs` 的，而 native
records `recsN` 也与 `recs` 同 nominal 半径 ⇒ `hdistC_of_native_P6CD` 的 `hnomId` 槽。取
`recs := recsN := d.native.records` 时第二个前提是 `fun _ _ _ => rfl`。 -/
theorem hnomId_of_ref_P6NI {K : ℕ → RetainedCoreHistory.{u}} {T₀ : ℕ → ℝ}
    {p : ℕ → CutoffParameters} {q q' : CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {recs : ∀ n (i : Fin (K n).eventCount), GeometricCutoffRecord (K n).toHistory i q}
    {recsN : ∀ n (i : Fin (K n).eventCount), GeometricCutoffRecord (K n).toHistory i q'}
    (hnom : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) h,
      (recordsK n i hi).nominalRadius h = (recs n i).nominalRadius h)
    (hrecs : ∀ n (i : Fin (K n).eventCount) h,
      (recsN n i).nominalRadius h = (recs n i).nominalRadius h) :
    ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) h,
      (recordsK n i hi).nominalRadius h = (recsN n i).nominalRadius h :=
  fun n i hi h => (hnom n i hi h).trans (hrecs n i h).symm

/-- **consumer：`hdistC` ⇐ P5L 供给（带 nominal 合取）+ native 数据（`_P6NI`）**：取 `q := d.native.params`、
`recs := d.native.records`，`hδq / hρa` 来自 `d.native.delta_tendsto / radius_antitone`；
`hdistC_of_native_P6CD` 的 `recordsK hcanK hacc hrad hord hδK hnomId` 全由 `hP5L` 供给
（`hδK` 经 `recenter_delta_tail_of_common_P6CD`），余下输入 `hT₀ hTn hsel4` 与其余逐字。 -/
theorem hdistC_of_P5L_nominal_P6NI {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt (σ
        n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (d : GC.LongTime.Ch11.Pre841Data_C11K (fun n => (K n).toHistory) σ y R
      hRpos)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (r L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hTn : Tendsto (fun n => (Tn n : ℝ)) atTop atTop)
    (hsel4 : ∀ n, R n ≤ (d.native.params.neckRadius (Tn n) ^ 2)⁻¹)
    (hP5L : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T : ℝ, ∀ n, ∃ p : CutoffParameters,
      p.delta = d.native.params.delta ∧ p.neckRadius = d.native.params.neckRadius ∧
      p.fixed = d.native.params.fixed ∧
      p.recenterConstant = d.native.params.recenterConstant ∧ D ≤ p.modelRadius ∧
      p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records : ∀ i : Fin (K n).eventCount, T ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) ∧
      ∀ i hi, (records i hi).nominalRadius =
          (d.native.records n i).nominalRadius ∧
        (records i hi).delta =
          (d.native.records n i).delta ∧
        (records i hi).order =
          (d.native.records n i).order ∧
        (∀ α, HEq ((records i hi).neck α) ((d.native.records n i).neck α)) ∧
        (∀ b, ((records i hi).static b).neck.scale =
          ((d.native.records n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records i hi).static b).inclusion
              (((records i hi).static b).witness.cap z) =
            ((d.native.records n i).static b).inclusion
              (((d.native.records n i).static b).witness.cap z)) :
    ∃ (T₀ : ℕ → ℝ) (p : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)),
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
      (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧ (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
      ((∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
          n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
          n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono
                hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
                hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                  n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) := by
  obtain ⟨T₀, p, recordsK, hcanK, hacc, hrad, hord, -, -, hpδ, hprc, hrp⟩ :=
    RetainedCoreHistory.exists_lateKdata_of_P5L_antitone_nominal_P6NI (fun _ => (0 : ℝ))
      d.native.records hP5L d.native.delta_tendsto d.native.radius_antitone
  refine ⟨T₀, p, recordsK, hcanK, hacc, hrad, hord, fun hT₀ => ?_⟩
  exact hdistC_of_native_P6CD hjt htj σ y R hσ hRpos d Tn aSeed haT hsT has pT seedTrace r L hL
    hroom htime hsmall hclock hRr recordsK hcanK hacc hrad hord hT₀ hTn hsel4
    (recenter_delta_tail_of_common_P6CD hpδ hprc d.native.delta_tendsto)
    (hnomId_of_ref_P6NI (fun n i hi h => congrFun (hrp n i hi).1 h) (fun _ _ _ => rfl))

/-- consumer：astra 链的 P5L 供给（reparameterization 追踪版）喂
`exists_lateKdata_of_P5L_antitone_nominal_P6NI` 的 `hP5L`
（`K n := F.tower.history n`、`recs := records`）。 -/
example {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, GC.GeneralFlow.PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
      GeometricCutoffRecord (F.tower.history n).toHistory i q)
    (hfixed : q.fixed = pBase.fixed) (hrc : q.recenterConstant = pBase.recenterConstant)
    (hmi : ∀ (m : ℕ) (i : Fin (S.state (m + 1)).native.eventCount) (n : ℕ),
      (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ≤ (n : ℝ) →
      ∃ j : Fin (F.tower.history n).eventCount,
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        HEq (records n j).delta ((W m).fineRecords i).delta ∧
        HEq (records n j).order ((W m).fineRecords i).order ∧
        HEq (records n j).neck ((W m).fineRecords i).neck)
    (hblock : ∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
      ∃ m : ℕ, ∃ i : Fin (S.state (m + 1)).native.eventCount,
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        (F.tower.history n).time j.succ =
          (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
        (F.tower.history n).time j.succ ≤ (3 : ℝ) ^ m ∧
        MetricCutCapEvent.SamePresentation
          (GC.GeneralFlow.translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent
          ((F.tower.history n).toHistory.event j) ∧
        ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
          ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
            (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
              (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder
              (W m).fineParameters.modelAccuracy b'),
            HEq b b' ∧ raw.hasCanonicalWindow ∧
            raw.delta = (((W m).fineRecords i).static b).delta ∧
            raw.order = (((W m).fineRecords i).static b).order ∧
            HEq raw.neck (((W m).fineRecords i).static b).neck ∧
            raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric ∧
            raw.neck.scale = ((records n j).static b').neck.scale ∧
            (∀ z : ThreeBall, raw.inclusion (raw.witness.cap z) =
              ((records n j).static b').inclusion (((records n j).static b').witness.cap z)))
    (hcof : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder)
    (hlink : ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
      GC.LongTime.Ch11.linkedCanonicalWindow_C11E (((W k).fineRecords i).static b))
    (Q : ℕ → ℝ) (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) :
    ∃ (T₀ : ℕ → ℝ) (p : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (F.tower.history n).eventCount),
        T₀ n ≤ (F.tower.history n).time i.succ →
        GeometricCutoffRecord (F.tower.history n).toHistory i (p n)),
      ∀ n (i : Fin (F.tower.history n).eventCount)
        (hi : T₀ n ≤ (F.tower.history n).time i.succ),
        (recordsK n i hi).nominalRadius =
          (records n i).nominalRadius ∧
        (recordsK n i hi).delta =
          (records n i).delta ∧
        (recordsK n i hi).order =
          (records n i).order ∧
        (∀ α, HEq ((recordsK n i hi).neck α) ((records n i).neck α)) ∧
        (∀ b, ((recordsK n i hi).static b).neck.scale =
          ((records n i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((recordsK n i hi).static b).inclusion
              (((recordsK n i hi).static b).witness.cap z) =
            ((records n i).static b).inclusion
              (((records n i).static b).witness.cap z) := by
  obtain ⟨T₀, p, recordsK, -, -, -, -, -, -, -, -, hrp⟩ :=
    RetainedCoreHistory.exists_lateKdata_of_P5L_antitone_nominal_P6NI
      (K := fun n => F.tower.history n) Q records
      (GC.LongTime.Ch11.lateLinkedRecordsSupplyNom_of_astra_P6NI S W F q records hfixed hrc hmi
        hblock hcof hlink) hδq hρa
  exact ⟨T₀, p, recordsK, hrp⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
