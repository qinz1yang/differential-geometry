import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyTopP6HPB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblySeedVolP6HPB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingDomC11CL2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateCoreP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizeP6X

/-!
# `hcenE[hcompat]` 的消去：用 hcenE 槽自带的选择数据付 c 相容（O-CH11-HCENE，后缀 `_P6HC`）

HP6B 剩余槽 `hcenE`（`hP6bTwoLevelTime_of_slots_P6HPB` 的 binder）在 HREC6 的路线
`hcenE_of_noShortcut_late_P6H6 ∘ hrec6'_of_P5L_compat_P6H6` 下只剩 `hcompat`（c 与 event 时间的相容性，
`scale_K = c · scale_Ho`）。本文件**不做** ∀ c 的 `hcompat`，而是把它整体换掉：

* **`hcompat`（∀ c 形）对 c → 0 为假**（诚实说明，不在本文件证伪）：它要求
  `q.delta (time_Ho) ≤ 1/(2·max 1 (3/c k)·ρ(0)) ≈ c k/(6ρ(0))`，而线性 lateness
  `(k+1)/2 ≤ c k · Kh.time = time_Ho` 只约束 Ho 时间、不约束 `c`；只要有任意晚的 event，取 `c k ≪ δ(time_Ho)`
  即违反。顶层的 `c` 确实取遍小值：`P6LateTimeCoreP6TC` 的反证序列里 `c k = r k ^ 2`（Core 的抛物尺度），
  所以 hcenE 槽的 `∀ c` 是真需要的，不能加强前提。
* **付款数据就在 hcenE 槽内**：坏点 `¬ Good_K(σ k, y k)` 与 `k+1 ≤ R k = R_K(y k)`。HP6b 上下文的 HCS / TDS
  （`outerSupply_twoLevel_C11G2` @ `q₀`，Good 常数 `(Γ.ε, C1P6 std, C2P6 std, C_t*)`）经
  `canonical_rescale_P6X` / `derivative_rescale_P6X` 搬到 `Kh`：`R_K > c·ρ(cσ)⁻²` ⇒ Good_K。故坏点给
  **`(k+1)·ρ(time_Ho)² ≤ c k`**（G1 `hcompat_of_selection_P6HC`，PROVED，per-sequence）。
* **record scale**：P5L record（`p.delta = q.delta`、`p.neckRadius = q.neckRadius`）用
  `inv_two_mul_sq_lt_static_scale_record_delta_P6M3`（`ρ₁ := ρ(time)`，**不是** HREC6 的 `ρ(0)`；
  `ρ₀ := δ²ρ`）得 `scale_Ho > 1/(2δ⁴ρ²)`，于是 `c·scale_Ho ≥ (k+1)/(2δ⁴) ≥ (k+1)/2 > 6`（`k ≥ 11`）——
  `six_lt_mul_scale_of_selection_P6HC`。用 `ρ(time)` 而非 `ρ(0)` 正是绕开 `hcompat` 的关键：`ρ²` 两边相消。
* **`hrec6_of_selection_P6HC`**：per-sequence 的五合取 records（只对给定 `(ind, c, i)`，前提是 Ho 时间 → ∞ 与
  选择不等式 eventually）。
* **孪生 `hcenE_sel_P6HC`**：`hcenE_of_noShortcut_late_P6H6` 证明体照抄，`hrec` binder 换成
  `hP5L hδq hcan hder`（P5L supply + δ → 0 + HCS + TDS，同一 `q`）；结论与 hcenE 逐字相同。
* **G2 `hcenE_bad_P6HC`**：结论 = `hP6bTwoLevelTime_of_slots_P6HPB` 的 `hcenE` binder **逐字**（生成器从
  `P6HP6bAssemblyP6HPB.lean` 源文本切出并断言），**0 binder**（除 G1 的参数 `kk εP6`）：`F = F₀`
  （`rawSurgery_eq_of_tower_eq_C11KW`）、SCRS⁺ 的 `q₀ / hδ₀ / hP5L₀`、`outerSupply_twoLevel_C11G2` @ `q₀`
  （`C{1,2}ceil_le_C{1,2}P6_C11GT6`、`Ctime_le_p6Ctime_C11G7B`）、
  `hCs1 hCs2` ← `capCollar_le_C{1,2}P6_C11CL3`。
  `q₀ = q`（t ≥ 0）的识别**不需要**：outerSupply 直接实例化在 `q₀`（SCRS⁺ 第一组字段即其 `hq`）。
* consumers：`example` 把 `hcenE_bad_P6HC` 喂 `hP6bTwoLevelTime_of_slots_P6HPB`（G1）与
  `a12EnhancedFull_of_slots_P6HPB`（G3）及 seedVol 孪生（G1b / G3b）的 `hcenE` 槽——
  **hcenE 从剩余槽表消去**。

剩余槽表（HP6B G2 表更新）：`hgapJ`、`hgapJ8`、`hgapJF`、`hgapJF8`、`hfootE` + 共享选择子
`Csel / T₀sel / Qtsel`（+ `hmono`）+ `kk`、`εP6`；G3 另 `hspine‴`（Codex）。`hcenE` = 已付（本文件）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B p6BadC_C11G2 htransMBad_C11G7B)

namespace ObservedHistory

/-! ## 1. G1：坏点 ⇒ c 相容（PROVED） -/

/-- **坏点曲率上界**（`_P6HC`）：HCS + TDS（阈值 `q.neckRadius`）在重标度 history `Kh = H.rescale_P6N c` 上，
`¬ Good_K(v, z)` ⇒ `R_K(z) ≤ c · ρ(c v)⁻²`（`canonical_rescale_P6X` /
`derivative_rescale_P6X` 的逆否）。 -/
theorem scalar_le_of_notGood_P6HC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hcan : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (n : ℕ) {c : ℝ} (hc : 0 < c)
    (v : Icc (0 : ℝ) ((F.tower.history n).rescale_P6N c hc).toHistory.horizon)
    (z : (((F.tower.history n).rescale_P6N c hc).toHistory.stageAt v).Carrier)
    (hbad : ¬ ((F.tower.history n).rescale_P6N c hc).toHistory.HasSpatialCanonicalTimeControl
      ε C1 C2 Ctime v z) :
    metricScalarAt (((F.tower.history n).rescale_P6N c hc).toHistory.stageMetric
        (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage v) v) z ≤
      c * (q.neckRadius (c * (v : ℝ)) ^ 2)⁻¹ := by
  by_contra h
  rw [not_le] at h
  have hR : ((q.rescale_P6N c hc).neckRadius v ^ 2)⁻¹ <
      metricScalarAt (((F.tower.history n).rescale_P6N c hc).toHistory.stageMetric
        (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage v) v) z := by
    rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X hc q]
    exact h
  exact hbad ⟨(F.tower.history n).canonical_rescale_P6X hc (hcan n) v z hR,
    fun hlo hhi => (F.tower.history n).derivative_rescale_P6X hc
      (fun w x hlo' hhi' hR' =>
        GC.LongTime.Ch11.stageDerivative_of_timeDerivativeSupply_P6X hder n w x hlo' hhi' hR')
      v z hlo hhi hR⟩

/-- **G1 `hcompat_of_selection_P6HC`（PROVED，per-sequence）**：hcenE 槽的选择数据——坏点
`¬ Good_K(σ k, y k)` 与 `k+1 ≤ R k = R_K(y k)`——加 HCS / TDS（同一 `q.neckRadius`）⇒
`(k+1) · ρ(c k · σ k)² ≤ c k`，即 `c` 与 event 时间（`c k · σ k = time_Ho`）的相容性由坏点自身付出。
（HREC6 的 `hcompat` 是 ∀ c 形且对 c → 0 为假；本不等式只对**选择出的**序列成立，正是 hcenE 需要的。） -/
theorem hcompat_of_selection_P6HC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hcan : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) :
    let Kh : ℕ → ObservedHistory.{u} := fun k =>
      ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
    ∀ (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
      (R : ℕ → ℝ),
      (∀ k, R k =
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
      (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
      (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
      ∀ k : ℕ, ((k : ℝ) + 1) * q.neckRadius (c k * (σ k : ℝ)) ^ 2 ≤ c k := by
  intro Kh σ y R hRdef hRr hbad k
  have h := scalar_le_of_notGood_P6HC hcan hder (ind k) (hc k) (σ k) (y k) (hbad k)
  have ht : 0 ≤ c k * (σ k : ℝ) := mul_nonneg (hc k).le (σ k).2.1
  have hρ : 0 < q.neckRadius (c k * (σ k : ℝ)) ^ 2 := pow_pos (q.neckRadius_pos _ ht) 2
  have h2 : (k : ℝ) + 1 ≤ c k * (q.neckRadius (c k * (σ k : ℝ)) ^ 2)⁻¹ :=
    (hRr k).trans ((hRdef k).le.trans h)
  rw [← div_eq_mul_inv, le_div_iff₀ hρ] at h2
  exact h2

/-- **record scale 由选择不等式付**（`_P6HC`）：record 的 `Λ·δ(time) ≤ 1/2` 且
`κ · ρ(time)² ≤ c`、`12 ≤ κ` ⇒ `6 < c · scale_Ho`（`inv_two_mul_sq_lt_static_scale_record_delta_P6M3`，
`ρ₁ := ρ(time)`、`ρ₀ := δ²ρ`：`c · scale ≥ κρ² · (2δ⁴ρ²)⁻¹ = κ/(2δ⁴) ≥ κ/2 ≥ 6`）。 -/
theorem six_lt_mul_scale_of_selection_P6HC {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {i : Fin H.eventCount} (Rc : GeometricCutoffRecord H.toHistory i p) {c κ : ℝ}
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hsel : κ * p.neckRadius (H.time i.succ) ^ 2 ≤ c) (hκ : 12 ≤ κ)
    (b : (H.toHistory.event i).RetainedBoundaryIndex) :
    6 < c * (Rc.static b).neck.scale := by
  have ht : 0 ≤ H.time i.succ := H.toHistory.time_nonneg i.succ
  have hδ0 := p.delta_pos _ ht
  have hδ1 := p.delta_lt_one _ ht
  have hρ0 := p.neckRadius_pos _ ht
  set δ := p.delta (H.time i.succ)
  set ρ := p.neckRadius (H.time i.succ)
  have hS := RetainedCoreHistory.inv_two_mul_sq_lt_static_scale_record_delta_P6M3 Rc
    (δ₀ := δ) (ρ₁ := ρ) (ρ₀ := δ ^ 2 * ρ) hΛδ le_rfl le_rfl le_rfl b
  set S := (Rc.static b).neck.scale
  have hSpos : 0 < S := (Rc.static b).neck.scale_pos
  have hκρ : 0 < κ * ρ ^ 2 := by positivity
  have hδ4 : δ ^ 4 ≤ 1 := pow_le_one₀ hδ0.le hδ1.le
  have hA : κ * ρ ^ 2 * (2 * (δ ^ 2 * ρ) ^ 2)⁻¹ = κ / (2 * δ ^ 4) := by
    field_simp
  have h6 : 6 ≤ κ / (2 * δ ^ 4) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h1 : κ * ρ ^ 2 * (2 * (δ ^ 2 * ρ) ^ 2)⁻¹ < κ * ρ ^ 2 * S :=
    mul_lt_mul_of_pos_left hS hκρ
  have h2 : κ * ρ ^ 2 * S ≤ c * S := mul_le_mul_of_nonneg_right hsel hSpos.le
  linarith

/-- **per-sequence 五合取 records**（`_P6HC`）：P5L supply + `δ → 0` + Ho 时间 → ∞ + 选择不等式
`(k+1)·ρ(time_Ho)² ≤ c k`（eventually）⇒ `hrec6` 的五合取结论（只对给定的 `(ind, c, i)`）。 -/
theorem hrec6_of_selection_P6HC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0)) (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) :
    let Kh : ℕ → ObservedHistory.{u} := fun k =>
      ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
    ∀ i : ∀ k, Fin (Kh k).eventCount,
      Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
      (∀ᶠ k : ℕ in atTop,
        ((k : ℝ) + 1) * q.neckRadius (c k * (Kh k).time (i k).succ) ^ 2 ≤ c k) →
      ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
      ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
        (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
          Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale := by
  intro Kh i hlate hsel εcap Rcap mcap hεcap
  obtain ⟨T, hT⟩ := hP5L Rcap εcap mcap hεcap
  have hΛ : 0 < q.recenterConstant := by linarith [q.recenterConstant_ge_four]
  obtain ⟨Tδ, hTδ⟩ := Filter.eventually_atTop.mp
    (hδq.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * q.recenterConstant))))
  have e : ∀ k, c k * (Kh k).time (i k).succ = (F.tower.history (ind k)).time (i k).succ :=
    fun k => mul_div_cancel₀ _ (hc k).ne'
  have hev : ∀ᶠ k in atTop, max T Tδ ≤ (F.tower.history (ind k)).time (i k).succ := by
    filter_upwards [hlate.eventually_ge_atTop (max T Tδ)] with k hk
    exact e k ▸ hk
  filter_upwards [hev, hsel, eventually_ge_atTop 11] with k hk hks hk11
  obtain ⟨p, hpδ, hpρ, -, hprc, hD, hacc, hord, records, hlink⟩ := hT (ind k)
  have hkT : T ≤ (F.tower.history (ind k)).time (i k).succ := (le_max_left _ _).trans hk
  have hkδ : q.delta ((F.tower.history (ind k)).time (i k).succ) ≤
      1 / (2 * q.recenterConstant) := hTδ _ ((le_max_right _ _).trans hk)
  refine ⟨p.rescale_P6N (c k) (hc k), (records (i k) hkT).rescale_P6M (c k) (hc k),
    fun b => ?_, hacc, hD, hord, fun b => ?_⟩
  · exact ((records (i k) hkT).static b).hasCanonicalWindow_rescale_P6M
      (GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _ (hlink (i k) hkT b))
      (c k) (hc k)
  · have hΛδ : p.recenterConstant * p.delta ((F.tower.history (ind k)).time (i k).succ) ≤
        1 / 2 := by
      rw [hprc, hpδ]
      have h1 := (le_div_iff₀ (by positivity)).1 hkδ
      linarith
    have hsel' : ((k : ℝ) + 1) * p.neckRadius ((F.tower.history (ind k)).time (i k).succ) ^ 2 ≤
        c k := by
      rw [hpρ, ← e k]
      exact hks
    have h12 : (12 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (11 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk11
      linarith
    have e2 : (((records (i k) hkT).rescale_P6M (c k) (hc k)).static b).neck.scale =
        c k * ((records (i k) hkT).static b).neck.scale :=
      ((records (i k) hkT).static b).rescale_P6M_scale (c k) (hc k)
    rw [e2]
    exact six_lt_mul_scale_of_selection_P6HC (records (i k) hkT) hΛδ hsel' h12 b

/-! ## 1b. 孪生：hcenE 结论逐字（per-sequence records） -/

/-- **孪生 `hcenE_sel_P6HC`（PROVED 条件形，binder 全为已付供给）**：`hcenE_of_noShortcut_late_P6H6` 的证明体
照抄，`hrec`（∀ c 的 `hrec6'`）换成 per-sequence 的 `hrec6_of_selection_P6HC`，其选择不等式由
`hcompat_of_selection_P6HC`（坏点 `hsel` + `R k ≥ k+1` + HCS / TDS）付。binder：`hCs1 hCs2`（collar 常数，
CL3 付）、同一 `qq` 的 P5L supply / `δ → 0` / HCS / TDS（SCRS⁺ + outerSupply 付）。结论 = `hcenE` 逐字。 -/
theorem hcenE_sel_P6HC {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (qq : CutoffParameters) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {C1f C2f m : ℝ} {kk : ℕ} (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hCs1 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C1)
    (hCs2 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C2)
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F qq)
    (hδq : Tendsto qq.delta atTop (𝓝 0))
    (hcan : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F qq.neckRadius ε C1 C2)
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F qq.neckRadius Ctime) :
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
          ∀ D : ((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
          ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) (Kh k).horizon) (z : ((Kh k).stageAt t).Carrier),
            (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed k ≤ t) (hvt : t ≤ Tn k),
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
                ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono hvt)) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / (4 * Real.sqrt (R k))) := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood hwin hwin' hroom hradii i hi
  have hlate : ∀ k : ℕ, ((k : ℝ) + 1) / 2 ≤ c k * (Kh k).time (i k).succ := by
    intro k
    have hck := hc k
    have has' : (aSeed k : ℝ) ≤ σ k := Subtype.coe_le_coe.mpr (has k)
    have hcl := hclock k
    have h1k := h1 k
    have hT := hTc k
    rw [← hi k]
    nlinarith [mul_le_mul_of_nonneg_left has' hck.le,
      mul_nonneg hck.le (by nlinarith : (0 : ℝ) ≤ (Tn k : ℝ) - 2)]
  obtain ⟨ε₀, hε₀, hseedprot⟩ := exists_seed_not_mem_innerWindow_P6HE.{u}
  obtain ⟨Rcap, mcap, εcap, -, hεcap, hRcap, hcolev⟩ :=
    GC.LongTime.Ch11.capCollar_of_record_P6HE.{u} hε hε'
  have hselK : ∀ k : ℕ,
      ((k : ℝ) + 1) * qq.neckRadius (c k * (Kh k).time (i k).succ) ^ 2 ≤ c k := by
    intro k
    have h := hcompat_of_selection_P6HC hcan hder ind c hc σ y R hRdef hRr hsel k
    rwa [hi k] at h
  have hrecEv := hrec6_of_selection_P6HC hP5L hδq ind c hc i (tendsto_of_late_P6H6 hlate)
    (Eventually.of_forall hselK) (min (min (1 / 2) ε₀) εcap) Rcap (max mcap 2)
    (lt_min (lt_min (by norm_num) hε₀) hεcap)
  have haσ : ∀ᶠ k in atTop, aSeed k < σ k := by
    filter_upwards [hwin 1 one_pos] with k hk
    have h0 : (0 : ℝ) < 1 / R k := by
      have := hRpos k
      positivity
    exact Subtype.coe_lt_coe.mp (by linarith)
  have hLpos : ∀ᶠ k in atTop, 0 < L k := hL.eventually_gt_atTop 0
  filter_upwards [hrecEv, haσ, hLpos] with k hk haσk hLk
  obtain ⟨pp, Rc, hcan, hacc, hrad, hord, hscale⟩ := hk
  have hacc1 : pp.modelAccuracy ≤ 1 / 2 := hacc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hacc2 : pp.modelAccuracy ≤ ε₀ := hacc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hacc3 : pp.modelAccuracy ≤ εcap := hacc.trans (min_le_right _ _)
  have hord1 : mcap ≤ pp.modelOrder := (le_max_left _ _).trans hord
  have hord2 : 2 ≤ pp.modelOrder := (le_max_right _ _).trans hord
  have hD : StandardCap.transitionEnd + 10 < pp.modelRadius := hRcap.trans_le hrad
  have hcol := hcolev Rc hcan hacc3 hrad hord1 C1 C2 hCs1 hCs2
  have hseedk : ∀ (b : ((Kh k).event (i k)).RetainedBoundaryIndex)
      (h1' : (Kh k).activeStage (aSeed k) ≤ (i k).succ)
      (h2' : (i k).succ ≤ (Kh k).activeStage (Tn k)),
      (seedTrace k).point (i k).succ h1' h2' ∉ (Rc.static b).window ''
        {x : standardCapWindow pp.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10} :=
    fun b h1' h2' => hseedprot Rc hcan hacc2 hord2 hD hscale
      ((Kh k).seed_scalar_succ_le_P6HE (i k) (haT k) (hsm k) (hclock k) (seedTrace k) (hsT k)
        (has k) (hi k) h1' h2') b
  have hδ : 0 < L k / (4 * Real.sqrt (R k)) := by
    have := Real.sqrt_pos.mpr (hRpos k)
    positivity
  exact (Kh k).hcenE_history_P6HE (i k) Rc hcan hacc1 hD hcol (haT k) (seedTrace k) (hsT k)
    (has k) (hi k) haσk hseedk (y k) (hsel k) hδ

/-! ## 2. G2：HP6B `hcenE` 槽逐字 @ c(Γ) 元组（0 binder） -/

/-- **G2 `hcenE_bad_P6HC`（PROVED）**：类型 = `hP6bTwoLevelTime_of_slots_P6HPB` 的 `hcenE` binder **逐字**
（`gen.py` 从 `P6HP6bAssemblyP6HPB.lean` 切出，`slot_hcenE.txt`）。参数只有 G1 的 `kk εP6`。证明：
`F = F₀`（`rawSurgery_eq_of_tower_eq_C11KW`）；SCRS⁺ 的 `q₀`、`hq₀`、`hδ₀`、`hP5L₀`；
`outerSupply_twoLevel_C11G2 … F q₀ hF hq₀` @ `(C1P6 std, C2P6 std, C_t*)` 给 HCS / TDS；`hCs1 hCs2` ←
`capCollar_le_C{1,2}P6_C11CL3`；`Γ.ε < 1/11` ← `Γ.epsilon_small`；然后孪生 `hcenE_sel_P6HC` @ `q₀`。
槽里的 `q`（tower 对角参数）不参与：hcenE 结论不含它。 -/
theorem hcenE_bad_P6HC (P : OrientedThreeStage.{u}) (g : P.Metric) (kk : ℕ)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 C1f C2f m : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      C1f = max (p6BadC_C11G2.{u} Γ) 9 + Real.sqrt (p6BadC_C11G2.{u} Γ) →
      C2f = 1200 * p6BadC_C11G2.{u} Γ → m = htransMBad_C11G7B.{u} Γ →
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
          ∀ D : ((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
          ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) (Kh k).horizon) (z : ((Kh k).stageAt t).Carrier),
            (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed k ≤ t) (hvt : t ≤ Tn k),
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
                ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono hvt)) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / (4 * Real.sqrt (R k)))
    := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 C1f C2f m
    Ctime hε1 hC1 hC2 hCt hC1f hC2f hm
  subst hε1 hC1 hC2 hCt hC1f hC2f hm
  obtain ⟨F₀, q₀, -, -, ⟨hF₀, hq₀, -⟩, -, -, ⟨-, -, hδ₀⟩, ⟨-, -, -, hP5L₀⟩, -⟩ := id hS
  have hFF : F = F₀ := GC.LongTime.Ch11.rawSurgery_eq_of_tower_eq_C11KW (hF.trans hF₀.symm)
  subst F₀
  obtain ⟨-, hcanS, -, hTD⟩ := GC.LongTime.Ch11.outerSupply_twoLevel_C11G2 hS hfine F q₀ hF hq₀
    (GC.LongTime.Ch11.C1ceil_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.C2ceil_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.Ctime_le_p6Ctime_C11G7B Γ)
  have hΓ : Γ.epsilon < 1 / 11 := by
    have := Γ.epsilon_small
    linarith
  exact hcenE_sel_P6HC F q₀ Γ.epsilon_pos hΓ (GC.LongTime.Ch11.capCollar_le_C1P6_C11CL3 Γ)
    (GC.LongTime.Ch11.capCollar_le_C2P6_C11CL3 Γ) hP5L₀ hδ₀ hcanS hTD

/-- **consumer（G2 → HP6B G1）**：`hcenE_bad_P6HC` 喂 `hP6bTwoLevelTime_of_slots_P6HPB` 的 `hcenE` 槽；
剩余参数 / 槽 = `kk εP6 hεP6 Csel T₀sel Qtsel hmono hgapJ hgapJ8 hgapJF hgapJF8 hfootE`（hcenE 消去）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) : True := by
  have _h := fun kk εP6 hεP6 Csel T₀sel Qtsel hmono hgapJ hgapJ8 hgapJF hgapJF8 hfootE =>
    hP6bTwoLevelTime_of_slots_P6HPB P g kk εP6 hεP6 Csel T₀sel Qtsel hmono hgapJ hgapJ8 hgapJF
      hgapJF8 (hcenE_bad_P6HC P g kk εP6) hfootE
  trivial

/-- **consumer（G2 → HP6B G3，A12′）**：A12′ 当前最小 binder 形 = {hspine‴（Codex）} ∪
{`hgapJ hgapJ8 hgapJF hgapJF8 hfootE` + 选择子 + `kk εP6`}（hcenE 消去）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) : True := by
  have _h := fun hspine kk εP6 hεP6 Csel T₀sel Qtsel hmono hgapJ hgapJ8 hgapJF hgapJF8 hfootE =>
    a12EnhancedFull_of_slots_P6HPB P g hspine kk εP6 hεP6 Csel T₀sel Qtsel hmono hgapJ hgapJ8
      hgapJF hgapJF8 (hcenE_bad_P6HC P g kk εP6) hfootE
  trivial

/-- **consumer（G2 → HP6B G1b / G3b，seedVol 孪生）**：seedVol 版的 `hcenE` 槽与 G1 逐字相同（`verify.py`），
同一 `hcenE_bad_P6HC` 喂入；剩余 = `hgapJ hgapJ8 hgapJF hgapJF8 hfootE'` + 选择子（G3b 另 `hspine`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) : True := by
  have _h1 := fun kk εP6 hεP6 Csel T₀sel Qtsel hmono hgapJ hgapJ8 hgapJF hgapJF8 hfootE' =>
    hP6bTwoLevelTime_of_slots_seedVol_P6HPB P g kk εP6 hεP6 Csel T₀sel Qtsel hmono hgapJ hgapJ8
      hgapJF hgapJF8 (hcenE_bad_P6HC P g kk εP6) hfootE'
  have _h3 := fun hspine kk εP6 hεP6 Csel T₀sel Qtsel hmono hgapJ hgapJ8 hgapJF hgapJF8
      hfootE' =>
    a12EnhancedFull_of_slots_seedVol_P6HPB P g hspine kk εP6 hεP6 Csel T₀sel Qtsel hmono hgapJ
      hgapJ8 hgapJF hgapJF8 (hcenE_bad_P6HC P g kk εP6) hfootE'
  trivial

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
