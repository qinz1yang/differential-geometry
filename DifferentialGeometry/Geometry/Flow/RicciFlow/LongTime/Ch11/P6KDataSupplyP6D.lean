import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerBookkeeping
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepDefsC11W

/-!
# P6 收口主形的 K 层数据前提 (a)：树内生产者的 adapter（S-CH11-P6DATA G2，后缀 `_P6D`）

主形 `false_of_selection_eventSlab_Kdata_ctrl_P6M2` 的 (a) 组：`hinit hrecK hqcan hpar hscaleK hθcap
hpinchK0 hslabK hqR hnotK`（`hRt` 已由 P6BND `P6ClosureNoRtP6S` 去掉）。本文件给能证的逐项 adapter
（对照表见 `build-logs/resume/state-S-CH11-P6DATA.md` G1）：

* `nonempty_initialIdentification_prefixAt_P6D`：`hinit` ⇐ full-history 的 `InitialIdentification`
  （`InCutoffClass` 的第一分量 / `PreparedSpatialState.initial` / `ScaffoldState.initial`），不用
  `horizon < B`；
* `exists_recordsK_of_hasCanonicalCutoffRecords_P6D`：`recordsK / p / hrecK` ⇐
  `hasCanonicalCutoffRecords`（choose）；
* `isCanonicalCutoffRecordFamily_of_chain_P6D`：astra narrow tuple 的全链 records
  （`CutoffRecords_C11S F q` + S3 windows + `q.delta` / `q.neckRadius` antitone）⇒
  `(F.tower.history n)` 上 `p₀ := q`、`δb := q.delta 0`、`ρb := q.neckRadius 0` 的
  `IsCanonicalCutoffRecordFamily`；
  **注意 `hpar`（modelRadius ≥ n+1 等）对这个 `p₀ = q` 不成立**，见 G1 缺口；
* `hscaleK_of_family_P6D`：`hscaleK` ⇐ `inv_two_mul_sq_lt_static_scale` + `Λδ ≤ 1/2` + `ρb` 选小；
* `exists_params_P6D`：`qcan / θcap / D` 的参数选择；
* `exists_phi_eventSlabsPinched_P6D`：`hpinchK0` ⇐ `exists_admissiblePinchingFunction_for_identified_
  incomingSlabs`（Hamilton–Ivey，`phi` 只依赖 `P₀ g₀`，与 `B` 无关）；
* `eventSlabsDerivative_mono_P6D` / `eventSlabsDerivative_of_stage_P6D` /
  `eventSlabsDerivative_of_timeDerivativeControl_P6D`：`hslabK` ⇐ stageMetric 形导数界 ⇐ 外层
  `TimeDerivativeControl_C11W X`（`Inv_C11W.timeDerivative`，阈值 `(X.radius²)⁻¹`，常数 `C.Ctime`）；
* `exists_Kdata_P6D`：(a) 组里能供给的四项（`hinit hrecK hscaleK hpinchK0`）一次给出。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- **`hinit`**：full-history 的 initial identification 搬到前缀 `prefixAt k`
（`inCutoffClass_prefixAt` 的第一分量，不用 `horizon < B`）。 -/
theorem nonempty_initialIdentification_prefixAt_P6D {P₀ : OrientedThreeStage.{u}}
    {g₀ : P₀.Metric} (H : RetainedCoreHistory.{u}) (k : Fin (H.eventCount + 1))
    (h : Nonempty (InitialIdentification P₀ g₀ H.toHistory)) :
    Nonempty (InitialIdentification P₀ g₀ (H.prefixAt k).toHistory) := by
  obtain ⟨A⟩ := h
  have hc : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) (0 : Fin (k.val + 1)) = 0 :=
    Fin.ext (by simp)
  exact ⟨InitialIdentification.ofStageZero A (congrArg H.stage hc)
    (congr_arg_heq H.initialMetric hc)⟩

/-- **`recordsK / p / hrecK`**：`hasCanonicalCutoffRecords`（逐 `n`）⇒ 一族 records 与
`IsCanonicalCutoffRecordFamily`。 -/
theorem exists_recordsK_of_hasCanonicalCutoffRecords_P6D {K : ℕ → RetainedCoreHistory.{u}}
    {p₀ : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    (h : ∀ n, (K n).hasCanonicalCutoffRecords (p₀ n) (δb n) (ρb n)) :
    ∃ (p : ℕ → CutoffParameters)
      (recordsK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (p n)),
      ∀ n, (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (recordsK n) := by
  choose p recs hfam using fun n =>
    ((K n).hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily (p₀ n) (δb n)
      (ρb n)).mp (h n)
  exact ⟨p, recs, hfam⟩

/-- **`hscaleK`**：canonical record family + `Λδ ≤ 1/2` + `ρb` 选小
（`(n+1)·qcan·2ρb² ≤ 1`，`ρb > 0`）⇒ 每个 static neck 的 scale `≥ (n+1)·qcan`。 -/
theorem hscaleK_of_family_P6D {K : ℕ → RetainedCoreHistory.{u}} {p₀ p : ℕ → CutoffParameters}
    {δb ρb qcan : ℕ → ℝ} {recordsK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (p n)}
    (hrecK : ∀ n, (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (recordsK n))
    (hΛδ : ∀ n, (p₀ n).recenterConstant * δb n ≤ 1 / 2)
    (hρ : ∀ n : ℕ, 0 < ρb n ∧ ((n : ℝ) + 1) * qcan n * (2 * ρb n ^ 2) ≤ 1) :
    ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((recordsK n i).static b).neck.scale := by
  intro n i b
  have h := (hrecK n).inv_two_mul_sq_lt_static_scale (hΛδ n) i b
  have hx : 0 < 2 * ρb n ^ 2 := by have := (hρ n).1; positivity
  have h1 : ((n : ℝ) + 1) * qcan n ≤ (2 * ρb n ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ hx]
    exact (hρ n).2
  exact h1.trans h.le

/-- **`hslabK` 阈值单调**：`EventSlabsDerivative Ctime q k` 对更大的阈值 `q' ≥ q` 仍成立。 -/
theorem eventSlabsDerivative_mono_P6D {H : RetainedCoreHistory.{u}} {Ctime : ℝ≥0} {q q' : ℝ}
    {k : Fin (H.eventCount + 1)} (h : H.EventSlabsDerivative Ctime q k) (hq : q ≤ q') :
    H.EventSlabsDerivative Ctime q' k :=
  fun j hj y t ht hR => h j hj y t ht (hq.trans_lt hR)

/-- **`hslabK`（stageMetric 形 ⇒ incoming-scalar 形）**：每个 event slab（stage `i.castSucc`，
开区间 `(time i.castSucc, time i.succ)`）上，`metricScalarAt (stageMetric …) y > q` 时
`|∂ₜ R| ≤ Ctime · R²` ⇒ `EventSlabsDerivative Ctime q (Fin.last _)`。 -/
theorem eventSlabsDerivative_of_stage_P6D (H : RetainedCoreHistory.{u}) {Ctime : ℝ≥0} {q : ℝ}
    (hstage : ∀ (i : Fin H.eventCount) (y : (H.stage i.castSucc).Carrier) (τ : ℝ),
      τ ∈ Ioo (H.time i.castSucc) (H.time i.succ) →
      q < metricScalarAt (H.toHistory.stageMetric i.castSucc τ) y →
      |derivWithin (fun v => metricScalarAt (H.toHistory.stageMetric i.castSucc v) y) (Iic τ) τ| ≤
        Ctime * metricScalarAt (H.toHistory.stageMetric i.castSucc τ) y ^ 2) :
    H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) := by
  intro j _ y t ht hR
  have h := hstage j y t ht (by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hR)
  simp only [ObservedHistory.stageMetric_castSucc_apply] at h
  exact h

/-- **`hslabK`（外层 `Inv_C11W.timeDerivative` ⇒ `EventSlabsDerivative`）**：
`TimeDerivativeControl_C11W X`（阈值 `(X.radius²)⁻¹`，常数 `C.Ctime`；W1L3
`derivative_bound_on_old_native_tail` 逐块维护）在 `(X.radius²)⁻¹ ≤ q` 时给出 `X.history` 的
`EventSlabsDerivative C.Ctime q`。 -/
theorem eventSlabsDerivative_of_timeDerivativeControl_P6D {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric} {m : ℕ}
    (X : GC.LongTime.Ch11.BlockState_C11W pBase C P g m)
    (hX : GC.LongTime.Ch11.TimeDerivativeControl_C11W X) {q : ℝ} (hq : (X.radius ^ 2)⁻¹ ≤ q) :
    X.history.EventSlabsDerivative C.Ctime q (Fin.last X.history.eventCount) := by
  refine eventSlabsDerivative_of_stage_P6D X.history fun i y τ hτ hR => ?_
  have hend : X.history.toHistory.stageEndTime i.castSucc = X.history.time i.succ := by
    rw [ObservedHistory.stageEndTime_castSucc]
  have hτ' : τ ∈ Ioo (X.history.time i.castSucc) (X.history.toHistory.stageEndTime i.castSucc) := by
    rw [hend]
    exact hτ
  exact hX i.castSucc y τ hτ' (hq.trans_lt hR)

/-- **chain 的全体 events records ⇒ `IsCanonicalCutoffRecordFamily`**：astra narrow tuple 的
`records : CutoffRecords_C11S F q`（同一 `q`，全体 history、全体 event）+ S3 windows + `q.delta` /
`q.neckRadius` 在 `[0, ∞)` 上 antitone ⇒ 取 `p₀ := q`、`δb := q.delta 0`、`ρb := q.neckRadius 0`。
（这个 family 的 `p₀ = q` 只有**固定** model window；主形的 `hpar` 要 modelRadius ≥ n+1 等，对它不成立，
见 state G1 缺口。） -/
theorem isCanonicalCutoffRecordFamily_of_chain_P6D {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hwin : GC.LongTime.Ch11.CanonicalWindowsSupply_C11S records)
    (hδ : AntitoneOn q.delta (Ici 0)) (hρ : AntitoneOn q.neckRadius (Ici 0)) (n : ℕ) :
    (F.tower.history n).IsCanonicalCutoffRecordFamily q (q.delta 0) (q.neckRadius 0)
      (records n) := by
  have h0 : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.mpr le_rfl
  refine ⟨rfl, rfl, rfl, rfl, rfl, hwin n, fun i => ?_, fun i => ?_⟩
  · exact hδ h0 (mem_Ici.mpr ((F.tower.history n).toHistory.time_nonneg i.succ))
      ((F.tower.history n).toHistory.time_nonneg i.succ)
  · exact hρ h0 (mem_Ici.mpr ((F.tower.history n).toHistory.time_nonneg i.succ))
      ((F.tower.history n).toHistory.time_nonneg i.succ)

end RetainedCoreHistory

/-- **参数选择**：`qcan n = max (n+1) (Q n)`（`Q n` = 导数界阈值）、`θcap n = 1 − 1/(n+2)`、
`D n = n+1`。主形的 `hqcan`（`n+1 ≤ qcan n`）、`hθcap`、`hpar` 里的 `n+1 ≤ D n` 随之成立，并且
`Q n ≤ qcan n`（`hslabK` 的阈值单调用）。 -/
theorem exists_params_P6D (Q : ℕ → ℝ) :
    ∃ qcan θcap D : ℕ → ℝ, (∀ n, qcan n = max ((n : ℝ) + 1) (Q n)) ∧
      (∀ n, θcap n = 1 - 1 / ((n : ℝ) + 2)) ∧ (∀ n, D n = (n : ℝ) + 1) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) ∧ (∀ n, Q n ≤ qcan n) ∧
      (∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) ∧ (∀ n : ℕ, (n : ℝ) + 1 ≤ D n) :=
  ⟨fun n => max ((n : ℝ) + 1) (Q n), fun n => 1 - 1 / ((n : ℝ) + 2), fun n => (n : ℝ) + 1,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => le_max_left _ _, fun _ => le_max_right _ _,
    fun _ => le_rfl, fun _ => le_rfl⟩

/-- **`hpinchK0`**：Hamilton–Ivey pinching 的 `phi` 只依赖 `(P₀, g₀)`；任一带 initial identification
与（全体 events 的）cutoff records 的 `RetainedCoreHistory` 有 `EventSlabsPinched phi`
（`event_initial` 给出 incoming slab 的 initial metric 条件）。 -/
theorem exists_phi_eventSlabsPinched_P6D (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
      ∀ (H : RetainedCoreHistory.{u}), Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      ∀ (p : CutoffParameters), (∀ i, GeometricCutoffRecord H.toHistory i p) →
      H.EventSlabsPinched phi := by
  obtain ⟨phi, hphi, h⟩ := Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs
    P₀ g₀
  refine ⟨phi, hphi, fun H hA p records j => ?_⟩
  obtain ⟨A⟩ := hA
  exact h H.toHistory A p records j.castSucc (H.time j.succ) (H.toHistory.event j).incoming
    (H.event_initial j)

/-- **(a) 组里能供给的四项一次给出**：`hinit`（前缀）、`hrecK`（含 `p` / `recordsK`）、`hscaleK`、
`hpinchK0`。数据：full-history 的 initial identification、`hasCanonicalCutoffRecords`、`Λδ ≤ 1/2`、
`ρb` 选小（`qcan` 任意）。`hpar` / `hqR` / `hnotK` / `hslabK` 不在其中（缺口 / 另给）。 -/
theorem exists_Kdata_P6D {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
    {K : ℕ → RetainedCoreHistory.{u}} (j : ∀ n, Fin (K n).eventCount)
    {p₀ : ℕ → CutoffParameters} {δb ρb qcan : ℕ → ℝ}
    (hinitK : ∀ n, Nonempty (InitialIdentification P₀ g₀ (K n).toHistory))
    (hcanon : ∀ n, (K n).hasCanonicalCutoffRecords (p₀ n) (δb n) (ρb n))
    (hΛδ : ∀ n, (p₀ n).recenterConstant * δb n ≤ 1 / 2)
    (hρ : ∀ n : ℕ, 0 < ρb n ∧ ((n : ℝ) + 1) * qcan n * (2 * ρb n ^ 2) ≤ 1) :
    ∃ (phi : ℝ → ℝ) (_ : Perelman.AdmissiblePinchingFunction phi) (p : ℕ → CutoffParameters)
      (recordsK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (p n)),
      (∀ n, Nonempty (InitialIdentification P₀ g₀ ((K n).prefixAt (j n).castSucc).toHistory)) ∧
      (∀ n, (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (recordsK n)) ∧
      (∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((recordsK n i).static b).neck.scale) ∧
      (∀ n, (K n).EventSlabsPinched phi) := by
  obtain ⟨p, recordsK, hrecK⟩ :=
    RetainedCoreHistory.exists_recordsK_of_hasCanonicalCutoffRecords_P6D hcanon
  obtain ⟨phi, hphi, hP⟩ := exists_phi_eventSlabsPinched_P6D P₀ g₀
  exact ⟨phi, hphi, p, recordsK,
    fun n => RetainedCoreHistory.nonempty_initialIdentification_prefixAt_P6D (K n) _ (hinitK n),
    hrecK, RetainedCoreHistory.hscaleK_of_family_P6D hrecK hΛδ hρ,
    fun n => hP (K n) (hinitK n) (p n) (recordsK n)⟩

/-- consumer（chain）：narrow tuple 的全链 records ⇒ 每个 `F.tower.history n` 的 canonical family，
再取 `hscaleK` 的 `ρb` 条件（`qcan` 与 `ρb` 的乘积界是仍显式的参数事实）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hwin : GC.LongTime.Ch11.CanonicalWindowsSupply_C11S records)
    (hδ : AntitoneOn q.delta (Ici 0)) (hρ : AntitoneOn q.neckRadius (Ici 0))
    (hΛδ : q.recenterConstant * q.delta 0 ≤ 1 / 2) (qcan : ℕ → ℝ)
    (hρ0 : 0 < q.neckRadius 0 ∧ ∀ n : ℕ,
      ((n : ℝ) + 1) * qcan n * (2 * q.neckRadius 0 ^ 2) ≤ 1) :
    ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale :=
  RetainedCoreHistory.hscaleK_of_family_P6D (K := fun n => F.tower.history n)
    (p₀ := fun _ => q) (p := fun _ => q) (δb := fun _ => q.delta 0) (ρb := fun _ => q.neckRadius 0)
    (recordsK := records)
    (fun n => RetainedCoreHistory.isCanonicalCutoffRecordFamily_of_chain_P6D records hwin hδ hρ n)
    (fun _ => hΛδ) (fun n => ⟨hρ0.1, hρ0.2 n⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
