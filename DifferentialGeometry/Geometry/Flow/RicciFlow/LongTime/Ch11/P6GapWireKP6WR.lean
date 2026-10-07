import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateSupplyAntiP6M3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.TimeDerivativeThresholdC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching

/-!
# hgapP K 层原尺度项的 producer adapter（S-CH11-P6WIRE G2a，后缀 `_P6WR`）

把已有 producer 的输出整理成 P6SEL3 `hgapP`（`P6NormalizePrefixP6X3`）K 层子句的形（对照表见
`build-logs/scratch/S-CH11-P6WIRE/TABLE.md` A1–A6）。**INTEGRATION-ONLY**，无新数学：

* `exists_initialHI_P6WR`（A4）：`a₀` 只依赖初始度量 `g`（紧性），每个 history 的 `initialMetric 0`
  都在 fixed HI region 里且 `−3/a₀ ≤ R`（`exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound`
  + `InitialIdentification.fixedHamiltonIveyRegion_and_scalar_lower_bound`）；
* `exists_lateThr_free_P6WR` / `lateThrFree_P6WR`（A2）：P5L 供给 `hP5L`（`∀ D ζ m, ∃ T, ∀ n, …`）
  在 history 层一致，故存在**与 history 子列 `ind` 无关**的阈值 `Tmin`：对任一 `ind` 与 `T₀ ≥ Tmin`，
  `K n := F.tower.history (ind n)` 上有 late records 及 `hcanK hacc hrad hord`、
  late neck scale `≥ S n`（`1 ≤ S n`）与 `hδF`（证明改编自 `exists_lateKdata_of_P5L_antitone_P6M3`，
  阈值取成 `max T₁ (max Tδ Tρ)`，`ρ` 只需 antitone）；
* `eventually_birth_P6WR`（A5）：`a₀ > 0` ⇒ eventually `1 ≤ a₀·(n+1)²`（`hbirthA` 的算术核）；
* `qcanSup_P6WR` / `eventSlabsDerivative_qcanSup_P6WR`（A6）：ch12 F2 阈值参数化
  `timeDerivativeSupply_of_astra_threshold_C12X`（阈值 `qcan_m`）+ 带上界 ⇒ `hslabK`，阈值
  `max_{m ≤ ⌈horizon⌉} qcan_m`（有限带，对每个 `n` 为常数）。`Qt/c` 须覆盖它是 P6 侧义务（S6）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **A4**：每个 history 的初始度量同属一个 fixed HI region（年龄 `a₀ > 0`，`n` 无关）。 -/
theorem exists_initialHI_P6WR {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ n x,
      InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x := by
  obtain ⟨a, ha, hfixed, hscalar⟩ := exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  refine ⟨a, ha, fun n x => ?_⟩
  have hzero := (F.tower.initial n).fixedHamiltonIveyRegion_and_scalar_lower_bound hfixed hscalar
  exact ⟨hzero.1 x, hzero.2 x⟩

/-- **A2（ind 无关阈值形）**：P5L 供给在 history 层 `n` 上一致（`hP5L : ∀ D ζ m, ∃ T, ∀ n, …`），
所以阈值 `Tmin` 不依赖 history 子列 `ind`；对任一 `ind` 与 `T₀ ≥ Tmin`，
`K n := F.tower.history (ind n)` 上有 late records 及 `hcanK hacc hrad hord`、scale `≥ S n`
（`1 ≤ S n`，目标与 `c` 无关）与 `hδF`。P6SEL3 G5 的 `T₀` 在 `ind` 之前取，故需要这个形。 -/
theorem exists_lateThr_free_P6WR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} (S : ℕ → ℝ) (hS1 : ∀ n, 1 ≤ S n)
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) :
    ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) → ∀ ind : ℕ → ℕ,
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
        (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
        (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
        (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
        (∀ (n : ℕ) i hi b, S n ≤ ((recordsK n i hi).static b).neck.scale) ∧
        (∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ n ≤ (F.tower.history (ind n)).time i.succ →
          q.delta ((F.tower.history (ind n)).time i.succ) ≤ 1 / ((n : ℝ) + 1)) := by
  choose T₁ hT₁ using fun n : ℕ =>
    hP5L ((n : ℝ) + 1) (1 / ((n : ℝ) + 1)) (n + 2) (by positivity)
  have hrc : 0 < q.recenterConstant := by linarith [q.recenterConstant_ge_four]
  have h2 : ∀ n : ℕ, ∃ T : ℝ, ∀ s ≥ T,
      q.delta s ≤ min (1 / ((n : ℝ) + 1)) (1 / (2 * q.recenterConstant)) := by
    intro n
    have hpos : (0 : ℝ) < min (1 / ((n : ℝ) + 1)) (1 / (2 * q.recenterConstant)) :=
      lt_min (by positivity) (by positivity)
    exact Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hpos))
  choose Tδ hTδ using h2
  have hSpos : ∀ n, 0 < S n := fun n => lt_of_lt_of_le one_pos (hS1 n)
  have hρ₁ : 0 < q.neckRadius 0 := q.neckRadius_pos 0 le_rfl
  have h3 : ∀ n : ℕ, ∃ T : ℝ, ∀ s ≥ T, q.delta s ≤ 1 / (2 * S n * q.neckRadius 0) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (2 * S n * q.neckRadius 0) :=
      div_pos one_pos (mul_pos (mul_pos two_pos (hSpos n)) hρ₁)
    exact Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hpos))
  choose Tρ hTρ using h3
  refine ⟨fun n => max (T₁ n) (max (Tδ n) (Tρ n)), fun T₀ hT ind => ?_⟩
  choose p hpδ hpρ hpfix hprc hprad hpacc hpord records hlink using fun n => hT₁ n (ind n)
  have hle1 : ∀ n s, T₀ n ≤ s → T₁ n ≤ s := fun n s h =>
    ((le_max_left _ _).trans (hT n)).trans h
  have hle2 : ∀ n s, T₀ n ≤ s → Tδ n ≤ s := fun n s h =>
    (((le_max_left _ _).trans (le_max_right _ _)).trans (hT n)).trans h
  have hle3 : ∀ n s, T₀ n ≤ s → Tρ n ≤ s := fun n s h =>
    (((le_max_right _ _).trans (le_max_right _ _)).trans (hT n)).trans h
  refine ⟨p, fun n i hi => records n i (hle1 n _ hi),
    fun n i hi b => GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _
      (hlink n i (hle1 n _ hi) b), hpacc, hprad, hpord, ?_, ?_⟩
  · intro n i hi b
    have hδs := hTδ n _ (hle2 n _ hi)
    have hρs := hTρ n _ (hle3 n _ hi)
    have ht0 : 0 ≤ (F.tower.history (ind n)).time i.succ :=
      (F.tower.history (ind n)).toHistory.time_nonneg i.succ
    have hdel1 : q.delta ((F.tower.history (ind n)).time i.succ) < 1 := q.delta_lt_one _ ht0
    have hdel0 : 0 < q.delta ((F.tower.history (ind n)).time i.succ) := q.delta_pos _ ht0
    have hρle : q.neckRadius ((F.tower.history (ind n)).time i.succ) ≤ q.neckRadius 0 :=
      hρa (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0) ht0
    have hδρ : q.delta ((F.tower.history (ind n)).time i.succ) ^ 2 * q.neckRadius 0 ≤
        1 / (2 * S n) := by
      have hc := hSpos n
      have h1 : q.delta ((F.tower.history (ind n)).time i.succ) * q.neckRadius 0 ≤
          1 / (2 * S n) := by
        have h2 := (le_div_iff₀ (by positivity)).1 hρs
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have h3 : q.delta ((F.tower.history (ind n)).time i.succ) ^ 2 * q.neckRadius 0 ≤
          q.delta ((F.tower.history (ind n)).time i.succ) * q.neckRadius 0 := by
        have : q.delta ((F.tower.history (ind n)).time i.succ) ^ 2 ≤
            q.delta ((F.tower.history (ind n)).time i.succ) := by nlinarith
        exact mul_le_mul_of_nonneg_right this hρ₁.le
      exact h3.trans h1
    have hΛδ' : (p n).recenterConstant * q.delta ((F.tower.history (ind n)).time i.succ) ≤
        1 / 2 := by
      rw [hprc n]
      have h1 : q.delta ((F.tower.history (ind n)).time i.succ) ≤ 1 / (2 * q.recenterConstant) :=
        hδs.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    have hlt := RetainedCoreHistory.inv_two_mul_sq_lt_static_scale_record_delta_P6M3
      (records n i (hle1 n _ hi))
      (δ₀ := q.delta ((F.tower.history (ind n)).time i.succ)) (ρ₁ := q.neckRadius 0)
      (ρ₀ := 1 / (2 * S n)) hΛδ' (by rw [hpδ n]) (by rw [hpρ n]; exact hρle) hδρ b
    have heq : (2 * (1 / (2 * S n)) ^ 2)⁻¹ = 2 * S n ^ 2 := by
      have := (hSpos n).ne'
      field_simp
    rw [heq] at hlt
    change S n ≤ ((records n i (hle1 n _ hi)).static b).neck.scale
    nlinarith [hS1 n]
  · intro n i hi
    exact (hTδ n _ (hle2 n _ hi)).trans (min_le_left _ _)

/-- 阈值 `Tmin`（`exists_lateThr_free_P6WR` 的见证，与 `ind` 无关）。 -/
def lateThrFree_P6WR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} (S : ℕ → ℝ) (hS1 : ∀ n, 1 ≤ S n)
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) : ℕ → ℝ :=
  Classical.choose (exists_lateThr_free_P6WR S hS1 hP5L hδq hρa)

/-- **A5**：`a₀ > 0` ⇒ eventually `1 ≤ a₀·(n+1)²`（`hbirthA` 的算术核）。 -/
theorem eventually_birth_P6WR {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ a₀ * (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
  refine Filter.eventually_atTop.mpr ⟨⌈1 / a₀⌉₊, fun n hn => ?_⟩
  have h1 : 1 / a₀ ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  have h2 : 1 ≤ a₀ * (n : ℝ) := by
    rw [div_le_iff₀ ha₀] at h1
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3 : (n : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) := by nlinarith
  calc (1 : ℝ) ≤ a₀ * (n : ℝ) := h2
    _ ≤ a₀ * (((n : ℝ) + 1) * ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left h3 ha₀.le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

open GC.GeneralFlow Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **A6 阈值**：前 `⌈v⌉₊ + 1` 个几何带的 `qcan` 的最大值（`v ↦` 非减）。 -/
def qcanSup_P6WR {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (v : ℝ) : ℝ :=
  (Finset.range (⌈v⌉₊ + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun m => (S.state m).prepared.qcan)

theorem qcanSup_mono_P6WR {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    {v w : ℝ} (h : v ≤ w) : qcanSup_P6WR S v ≤ qcanSup_P6WR S w := by
  refine Finset.sup'_le _ _ fun m hm => Finset.le_sup' (fun m => (S.state m).prepared.qcan) ?_
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hm)
    (Nat.succ_le_succ (Nat.ceil_mono h)))

/-- 阈值函数 `qcanSup` 满足 ch12 F2 的 `hQ`：每个 `v ≥ 0` 落在某个带 `m`，且 `qcan_m ≤ qcanSup v`。 -/
theorem hQ_qcanSup_P6WR {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (v : ℝ) (hv : 0 ≤ v) :
    ∃ m : ℕ, preparedSpatialHorizon m ≤ v ∧ v < (3 : ℝ) ^ m ∧
      (S.state m).prepared.qcan ≤ qcanSup_P6WR S v := by
  obtain ⟨m, h1, h2⟩ := exists_band_C12X v hv
  refine ⟨m, h1, h2, ?_⟩
  have hm : m < ⌈v⌉₊ + 1 := by
    cases m with
    | zero => exact Nat.succ_pos _
    | succ k =>
      have hk : (k : ℝ) < v := (nat_lt_three_pow k).trans_le h1
      have hk' : k < ⌈v⌉₊ := by
        have := hk.trans_le (Nat.le_ceil v)
        exact_mod_cast this
      omega
  exact Finset.le_sup' (fun m => (S.state m).prepared.qcan) (Finset.mem_range.mpr hm)

/-- **A6（`hslabK` 的 chain 来源）**：narrow/outer chain 数据 + `F.tower = S.tower` ⇒ 每个
`n` 的 `(F.tower.history n).EventSlabsDerivative C.Ctime (qcanSup S horizon_n) last`。阈值是有限带的
`qcan` 最大值（ch12 F2 `timeDerivativeSupply_of_astra_threshold_C12X`），不是 `ρ⁻²`。 -/
theorem eventSlabsDerivative_qcanSup_P6WR {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (n : ℕ) :
    (F.tower.history n).EventSlabsDerivative C.Ctime
      (qcanSup_P6WR S (F.tower.history n).horizon) (Fin.last (F.tower.history n).eventCount) := by
  have h := timeDerivativeSupply_of_astra_threshold_C12X S εcut Dcut mcut W hshift hoffset F
    hTower (qcanSup_P6WR S) (hQ_qcanSup_P6WR S)
  intro j _ y t ht hR
  have htH : t ≤ (F.tower.history n).horizon :=
    ht.2.le.trans (((F.tower.history n).time_strictMono.monotone (Fin.le_last _)).trans
      (F.tower.history n).time_le_horizon)
  exact h.1 n j y t ht ((qcanSup_mono_P6WR S htH).trans_lt hR)

end GC.LongTime.Ch11
