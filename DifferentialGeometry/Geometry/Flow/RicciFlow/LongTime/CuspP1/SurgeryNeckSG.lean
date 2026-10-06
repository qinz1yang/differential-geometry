import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap

/-!
# neck 的 unchanged 侧（IMS07 / IAU02 的几何基础，G3，S-A14-SURGERY）

`GeometricCutoffRecord.static b : PresentedStaticCap` 在保留侧的 static neck 坐标
`z_s ∈ [0, δ_s⁻¹)`（`z_s = 0` 是切割球面，原 neck 坐标 `z = ±1`；蓝图的 "[0, δ⁻¹) × S²"）上给出
`retainedPoint`（落在 `retainedCore`）与 `retained_eq`（经 `presentation` 对应到
`inclusion (witness.retained x)`）。本文件证：

* `neck_chart_isOpenEmbedding_SG`：`NormalizedNeck.chart` 是开嵌入；
* `collar_mem_interior_retained_SG`：`0 < z_s < δ_s⁻¹` 的 collar 点在 `interior (val '' retainedCore)`；
* `collar_regularCrossing_SG`：该点与 `inclusion (witness.retained x)` 是 `RegularCrossing`；
* `exists_collar_partialDiffeomorph_SG`：开 collar `chart '' {0 < z_s < δ_s⁻¹}` 上的
  `PartialDiffeomorph F`（`terminalRegularOpen → Q`），`F ∘ chart = inclusion ∘ witness.retained`，
  `terminal.metric` 与 `outputMetric` 经 `F` 等距（"z ≥ z₀ 侧不变"）；
* `collar_length_gt_SG`、`exists_late_collar_SG`：`δ_s⁻¹ > 100`（蓝图 z=50 切片所需），晚期事件成立。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

section Neck

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
/-- `NormalizedNeck.chart`（`C(neckBuffer δ, M)`）是开嵌入（同维光滑嵌入）。 -/
theorem neck_chart_isOpenEmbedding_SG {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck h δ k) : Topology.IsOpenEmbedding N.chart :=
  ⟨N.chart_smooth.isEmbedding, Manifold.isOpen_range_of_isSmoothEmbedding
    (by simp [ThreeSpace]) N.chart_smooth⟩

/-- collar 的开核 `{0 < z < δ⁻¹} ⊆ neckBuffer δ`。 -/
def collarOpen_SG (δ : ℝ) : Set (neckBuffer δ) := {y | 0 < y.1.2 ∧ y.1.2 < δ⁻¹}

theorem isOpen_collarOpen_SG (δ : ℝ) : IsOpen (collarOpen_SG δ) :=
  (isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)).inter
    (isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const)

end Neck

section Event

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
  (R : GeometricCutoffRecord H i p) (b : (H.event i).RetainedBoundaryIndex)

/-- collar 的开像落在 `val '' retainedCore` 里（`retainedPoint` + `retained_point_eq`）。 -/
theorem collar_image_subset_retained_SG :
    Subtype.val '' ((R.static b).neck.chart '' collarOpen_SG (R.static b).delta) ⊆
      Subtype.val '' (H.event i).transition.trace.retainedCore := by
  rintro _ ⟨q, ⟨y, hy, rfl⟩, rfl⟩
  let x : neckRetainedCollar (R.static b).delta := ⟨y.1, hy.1.le, hy.2⟩
  have h := (R.static b).retained_point_eq x y.2
  exact ⟨(R.static b).retainedPoint x |>.1, (R.static b).retainedPoint x |>.2, h⟩

/-- `0 < z_s < δ_s⁻¹` 的 collar 点是 `interior (val '' retainedCore)` 的点。 -/
theorem collar_mem_interior_retained_SG (y : neckBuffer (R.static b).delta)
    (hy : y ∈ collarOpen_SG (R.static b).delta) :
    ((R.static b).neck.chart y).1 ∈
      interior (Subtype.val '' (H.event i).transition.trace.retainedCore) := by
  have hO : IsOpen (Subtype.val '' ((R.static b).neck.chart '' collarOpen_SG (R.static b).delta)) :=
    (H.event i).incoming.terminalRegularOpen.isOpen.isOpenMap_subtype_val _
      ((neck_chart_isOpenEmbedding_SG (R.static b).neck).isOpenMap _
        (isOpen_collarOpen_SG _))
  exact interior_maximal (collar_image_subset_retained_SG R b) hO ⟨_, ⟨y, hy, rfl⟩, rfl⟩

/-- collar 点与 `inclusion (witness.retained x)` 是 `RegularCrossing`（x 的坐标 = y 的坐标）。 -/
theorem collar_regularCrossing_SG (y : neckBuffer (R.static b).delta)
    (hy : y ∈ collarOpen_SG (R.static b).delta) :
    (H.event i).RegularCrossing ((R.static b).neck.chart y).1
      ((R.static b).inclusion ((R.static b).witness.retained ⟨y.1, hy.1.le, hy.2⟩)) := by
  obtain ⟨z, hz, hcross, hpres⟩ :=
    (H.event i).exists_oldTerminal_eq_of_mem_interior_retained R.old_eq_retained
      ((R.static b).neck.chart y) (collar_mem_interior_retained_SG R b y hy)
  let x : neckRetainedCollar (R.static b).delta := ⟨y.1, hy.1.le, hy.2⟩
  have hpt : z.1 = ((R.static b).retainedPoint x).1 := by
    apply Subtype.ext
    rw [← (H.event i).oldTerminal_eq z, hz]
    exact ((R.static b).retained_point_eq x y.2).symm
  have hout : (H.event i).oldOutput z =
      (R.static b).inclusion ((R.static b).witness.retained x) := by
    have h1 := (H.event i).oldOutput_eq z
    rw [hpt, (R.static b).retained_eq x] at h1
    exact (Sum.inl_injective h1).symm
  rw [← hout]
  exact hcross

/-- **neck 的 unchanged 侧（G3 主定理）。** 开 collar `chart '' {0 < z_s < δ_s⁻¹}` 上存在
`PartialDiffeomorph F : terminalRegularOpen → stage i.succ`：
`F ∘ chart = inclusion ∘ witness.retained`，`terminal.metric` 与 `outputMetric` 经 `F` 等距。 -/
theorem exists_collar_partialDiffeomorph_SG :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.stage i.succ).Carrier ∞,
      F.source = (R.static b).neck.chart '' collarOpen_SG (R.static b).delta ∧
      (∀ (y : neckBuffer (R.static b).delta) (hy : y ∈ collarOpen_SG (R.static b).delta),
        F ((R.static b).neck.chart y) =
          (R.static b).inclusion ((R.static b).witness.retained ⟨y.1, hy.1.le, hy.2⟩)) ∧
      ∀ x ∈ F.source, ∀ v w : TangentSpace ThreeModel x,
        (H.event i).outputMetric.inner (F x) (mfderiv ThreeModel ThreeModel (F : _ → _) x v)
          (mfderiv ThreeModel ThreeModel (F : _ → _) x w) =
        (H.event i).terminal.metric.inner x v w := by
  let N := (R.static b).neck
  let δ := (R.static b).delta
  have hδ : 0 < δ := N.delta_pos
  let W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen :=
    ⟨N.chart '' collarOpen_SG δ, (neck_chart_isOpenEmbedding_SG N).isOpenMap _
      (isOpen_collarOpen_SG δ)⟩
  let y₀ : neckBuffer δ := ⟨(N.sphereMark, δ⁻¹ / 2), by
    have := inv_pos.mpr hδ
    constructor <;> simp only <;> linarith⟩
  have hy₀ : y₀ ∈ collarOpen_SG δ := by
    have := inv_pos.mpr hδ
    constructor <;> simp only [y₀] <;> linarith
  have hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' (H.event i).old) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [R.old_eq_retained]
    exact collar_mem_interior_retained_SG R b y hy
  obtain ⟨F, hsrc, hcross, -, hmetric⟩ :=
    (H.event i).exists_survivor_partialDiffeomorph W ⟨N.chart y₀, y₀, hy₀, rfl⟩ hW
  refine ⟨F, hsrc, ?_, fun x hx v w => hmetric x (by rwa [hsrc] at hx) v w⟩
  intro y hy
  exact (H.event i).regularCrossing_right_unique (hcross _ ⟨y, hy, rfl⟩)
    (collar_regularCrossing_SG R b y hy)

/-- 小 δ ⇒ static neck 的 collar 长度 `δ_s⁻¹ > 100`（蓝图 `z = 50` 切片所需）：
`δ_s = recenterConstant · δ_α ≤ recenterConstant · parameters.delta (time i.succ)`。 -/
theorem collar_length_gt_SG
    (hδ : p.recenterConstant * p.delta (H.time i.succ) < 1 / 100) :
    100 < ((R.static b).delta)⁻¹ := by
  have h1 : (R.static b).delta = p.recenterConstant * R.delta b.1.1 := R.recenter_delta b
  have h2 : R.delta b.1.1 ≤ p.delta (H.time i.succ) := R.delta_le b.1.1
  have hc : 0 < p.recenterConstant := by linarith [p.recenterConstant_ge_four]
  have h3 : (R.static b).delta ≤ p.recenterConstant * p.delta (H.time i.succ) := by
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 hc.le
  have hpos := (R.static b).neck.delta_pos
  rw [lt_inv_comm₀ (by norm_num) hpos]
  have : (R.static b).delta < 1 / 100 := lt_of_le_of_lt h3 hδ
  simpa using this

end Event

section Late

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- 晚期事件（`δ(t) → 0`）都满足 `δ_s⁻¹ > 100`。 -/
theorem exists_late_collar_SG (pr : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    ∃ B : ℝ, ∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      B < (F.tower.history n).toHistory.time i.succ →
        100 < (((pr.records n i).static b).delta)⁻¹ := by
  have hc : 0 < pr.parameters.recenterConstant := by
    linarith [pr.parameters.recenterConstant_ge_four]
  obtain ⟨B, hB⟩ := hdec (1 / (100 * pr.parameters.recenterConstant)) (by positivity)
  refine ⟨B, fun n i b hbt => collar_length_gt_SG (pr.records n i) b ?_⟩
  have h := hB _ hbt
  rw [pr.accuracy_eq]
  calc pr.parameters.recenterConstant * δ _
      < pr.parameters.recenterConstant * (1 / (100 * pr.parameters.recenterConstant)) :=
        mul_lt_mul_of_pos_left h hc
    _ = 1 / 100 := by field_simp

/-- **consumer：晚期事件的 neck unchanged 侧覆盖 `0 < z_s < 100`。** 每个晚期事件、每个保留边界 `b`：
开 collar 上的 `PartialDiffeomorph F`（`F ∘ chart = inclusion ∘ witness.retained`，
`terminal.metric ↔ outputMetric` 等距），且 `{0 < z_s < 100}`（蓝图 `z = 50` 的两侧缓冲）
整个在 collar 内。 -/
theorem exists_late_neck_unchanged_SG (pr : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    ∃ B : ℝ, ∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      B < (F.tower.history n).toHistory.time i.succ →
        (∀ y : neckBuffer ((pr.records n i).static b).delta, 0 < y.1.2 → y.1.2 < 100 →
          y ∈ collarOpen_SG ((pr.records n i).static b).delta) ∧
        ∃ Fd : PartialDiffeomorph ThreeModel ThreeModel
            ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen
            ((F.tower.history n).toHistory.stage i.succ).Carrier ∞,
          Fd.source = ((pr.records n i).static b).neck.chart ''
              collarOpen_SG ((pr.records n i).static b).delta ∧
          (∀ (y : neckBuffer ((pr.records n i).static b).delta)
            (hy : y ∈ collarOpen_SG ((pr.records n i).static b).delta),
            Fd (((pr.records n i).static b).neck.chart y) =
              ((pr.records n i).static b).inclusion
                (((pr.records n i).static b).witness.retained ⟨y.1, hy.1.le, hy.2⟩)) ∧
          ∀ x ∈ Fd.source, ∀ v w : TangentSpace ThreeModel x,
            ((F.tower.history n).toHistory.event i).outputMetric.inner (Fd x)
                (mfderiv ThreeModel ThreeModel (Fd : _ → _) x v)
                (mfderiv ThreeModel ThreeModel (Fd : _ → _) x w) =
              ((F.tower.history n).toHistory.event i).terminal.metric.inner x v w := by
  obtain ⟨B, hB⟩ := exists_late_collar_SG pr hdec
  refine ⟨B, fun n i b hbt => ⟨fun y h0 h1 => ⟨h0, h1.trans (hB n i b hbt)⟩, ?_⟩⟩
  exact exists_collar_partialDiffeomorph_SG (pr.records n i) b

end Late

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
