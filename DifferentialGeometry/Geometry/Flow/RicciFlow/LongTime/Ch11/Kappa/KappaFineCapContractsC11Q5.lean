import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ModelWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseProfile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

/-!
# fine-cap 合同：接口 (3)（O-CH11-FINECAP G1，后缀 `_C11Q5`）

R-C11-4 D-2 路线 (b′)：保留固定基础 `CutoffParameters`，由**同一顶实际插帽**、随 neck precision `δ` 改善的
fine-cap realization 支付窗口屏障的请求 `(D', m', ε')`。设计：
`docs/geometrization/chapter8/design-C11-finecap-20261007.md`。

* `FineCapRealization_C11Q5 S D' m' ε'`：`hasCanonicalWindow` 的扩大形——canonical witness 在请求
  `(D', m', ε')` 上、窗口嵌入 `J : standardCapWindow D' → Q`、实际 neck 尺度绑定、实际输出度量绑定、
  同一顶实际帽（`S.inclusion ∘ S.witness.cap`）。`D' = D, J = S.window` 即 `hasCanonicalWindow`
  （`fineCapRealization_of_hasCanonicalWindow_C11Q5`）。
* `ActualCanonicalInsertion_C11Q5 S`：三个绑定的源头证书——实际 neck 的 normalized datum `d`
  （`δ ≤ S.delta`、阶 `2⌊δ⁻¹⌋₊ + 4 ≤ k`、`scalar(x₀) = S.neck.scale`）与**整个**插入商空间
  `InsertionQuotient` 到实际输出的光滑嵌入 `J`，
  `J^*outputMetric = d.oriented.positiveSideInsertionMetric`，
  帽核 `adjunctionCell …` 覆盖实际帽。树内 `hasCanonicalWindow` 只在 D-窗口上绑定度量，推不出扩大窗口。
* **接口 (3)** `exists_fineCapRealization_of_actual_C11Q5`：
  `∀ (D' ≥ transitionEnd) m' (ε' > 0) ∃ δ_* > 0`，
  `ActualCanonicalInsertion S ∧ S.delta ≤ δ_* ⇒ FineCapRealization S D' m' ε'`。
  δ_* 由 producer 的三件给出：
  `exists_normalizedDatum_modelWindow_error_lt`（任意 `A`、任意阶 `k ≥ m'`）、`collapseTip_mem_buffer`、
  阶阈值 `(m'+1)⁻¹`；witness = `canonicalStaticInsertionWitness`（`outMetric`、`windowMap` 为 `rfl`）。
  这正是 `exists_uniform_positiveCoordinate_static_estimates` 的 δ 机制在
  `A = fixed.collarLength` 处的 per-A 版。
* record 对接：`staticCap_delta_le_C11Q5`（`S.delta = Λrec · δ_α ≤ Λrec · δ(t)`）、
  `fineCapRealization_of_record_C11Q5`（record 形的 (3)）。
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

local instance fact_finrank_three_C11Q5 : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

local instance quotientChartedSpace_C11Q5 {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (StandardCap.InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace StandardCap.transitionEnd_pos hB

local instance quotientIsManifold_C11Q5 {B : ℝ} {hB : 0 < B} :
    IsManifold ThreeModel ∞ (StandardCap.InsertionQuotient hB) :=
  radialCapAttachment_isManifold StandardCap.transitionEnd_pos hB

section Contracts

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

/-- **fine-cap realization**（接口 (3) 的结论）：实际帽 `S` 在请求 `(D', m', ε')` 上的 canonical window——
canonical witness `w`（A = `fixed.collarLength`）、窗口嵌入 `J`、实际 neck 尺度、实际输出度量、同一顶实际帽。 -/
def FineCapRealization_C11Q5 (S : E.PresentedStaticCap fixed D m ε b) (D' : ℝ) (m' : ℕ)
    (ε' : ℝ) : Prop :=
  ∃ (x₀ : E.incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
    (d : normalizedDatum E.terminal.metric x₀ δ k)
    (w : StandardCap.CanonicalStaticInsertionWitness d fixed.collarLength fixed.collar_pos D' m' ε')
    (J : standardCapWindow D' → Q.Carrier),
    IsSmoothEmbedding ThreeModel ThreeModel ∞ J ∧
    metricScalarAt E.terminal.metric x₀ = S.neck.scale ∧
    (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      S.neck.scale * E.outputMetric.inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z)) ∧
    ∀ z : ThreeBall, ∃ x : standardCapWindow D', ‖x.val‖ ≤ StandardCap.transitionEnd ∧
      J x = S.inclusion (S.witness.cap z)

/-- **实际 canonical 插入证书**（三个绑定的源头）：实际 neck 的 normalized datum `d`（precision 不劣于
`S.delta`，阶随 `δ⁻¹` 增长，尺度 = `S.neck.scale`）+ 整个插入商空间到实际输出的光滑嵌入 `J`，
`J^*outputMetric = d.oriented.positiveSideInsertionMetric`，帽核覆盖实际帽。 -/
def ActualCanonicalInsertion_C11Q5 (S : E.PresentedStaticCap fixed D m ε b) : Prop :=
  ∃ (x₀ : E.incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
    (d : normalizedDatum E.terminal.metric x₀ δ k) (hAB : 2 * fixed.collarLength < δ⁻¹)
    (J : StandardCap.InsertionQuotient (inv_pos.mpr d.precision_pos) → Q.Carrier),
    IsSmoothEmbedding ThreeModel ThreeModel ∞ J ∧
    metricScalarAt E.terminal.metric x₀ = S.neck.scale ∧
    δ ≤ S.delta ∧ 2 * ⌊δ⁻¹⌋₊ + 4 ≤ k ∧
    (∀ y (v z : TangentSpace ThreeModel y),
      (d.oriented.positiveSideInsertionMetric fixed.collar_pos hAB).inner y v z =
        E.outputMetric.inner (J y) (mfderiv ThreeModel ThreeModel J y v)
          (mfderiv ThreeModel ThreeModel J y z)) ∧
    ∀ z : ThreeBall, ∃ y : {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd},
      J (adjunctionCell (radialCapBoundary StandardCap.transitionEnd_pos)
        (retainedBoundary (inv_pos.mpr d.precision_pos)) y) = S.inclusion (S.witness.cap z)

/-- 粗 canonical window 是 fine realization 在 `(D, m, ε)` 处的特例（`J = S.window`）。 -/
theorem fineCapRealization_of_hasCanonicalWindow_C11Q5 (S : E.PresentedStaticCap fixed D m ε b)
    (hS : S.hasCanonicalWindow) : FineCapRealization_C11Q5 S D m ε := by
  obtain ⟨x₀, δ, k, d, w, hscale, hmetric, hcap⟩ := hS
  exact ⟨x₀, δ, k, d, w, S.window, S.window_smooth, hscale, hmetric, hcap⟩

end Contracts

/-- 阶阈值：`δ ≤ (m'+1)⁻¹` ⇒ `m' ≤ 2⌊δ⁻¹⌋₊ + 4`。 -/
theorem le_order_of_delta_le_C11Q5 {δ : ℝ} {m' k : ℕ} (hδ : 0 < δ)
    (hle : δ ≤ ((m' : ℝ) + 1)⁻¹) (hk : 2 * ⌊δ⁻¹⌋₊ + 4 ≤ k) : m' ≤ k := by
  have hm : ((m' : ℝ) + 1) ≤ δ⁻¹ := by
    have h := (inv_le_inv₀ (inv_pos.mpr (by positivity)) hδ).mpr hle
    rwa [inv_inv] at h
  have hfl : m' ≤ ⌊δ⁻¹⌋₊ := Nat.le_floor (by linarith)
  omega

/-- **接口 (3)**：实际 canonical 插入 + `S.delta ≤ δ_*(D', m', ε')` ⇒ 请求 `(D', m', ε')` 的 fine-cap
realization。`δ_* = min(δ_window, δ_tip, (m'+1)⁻¹)`；witness = `canonicalStaticInsertionWitness`，
窗口 = `J ∘ w.window`（链式法则 + 整体度量等式），帽 = `modelWindowMap_agrees_cap`。 -/
theorem exists_fineCapRealization_of_actual_C11Q5 (fixed : StaticCapScaffold) (D' : ℝ)
    (hD' : StandardCap.transitionEnd ≤ D') (m' : ℕ) (ε' : ℝ) (hε' : 0 < ε') :
    ∃ δs : ℝ, 0 < δs ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s} {D ε : ℝ}
        {m : ℕ} {b : E.RetainedBoundaryIndex} (S : E.PresentedStaticCap fixed D m ε b),
        ActualCanonicalInsertion_C11Q5 S → S.delta ≤ δs → FineCapRealization_C11Q5 S D' m' ε' := by
  have hD'pos : 0 < D' := StandardCap.transitionEnd_pos.trans_le hD'
  obtain ⟨δw, hδw, -, hwin⟩ := StandardCap.exists_normalizedDatum_modelWindow_error_lt
    fixed.collarLength fixed.collar_pos D' hD'pos m' ε' hε'
  have hM : 0 < 2 * fixed.collarLength + 5 * StandardCap.transitionEnd / 2 + 3 := by
    linarith [StandardCap.transitionEnd_pos, fixed.collar_pos]
  have hm1 : (0 : ℝ) < (m' : ℝ) + 1 := by positivity
  refine ⟨min δw (min (2 * fixed.collarLength + 5 * StandardCap.transitionEnd / 2 + 3)⁻¹
    ((m' : ℝ) + 1)⁻¹), lt_min hδw (lt_min (inv_pos.mpr hM) (inv_pos.mpr hm1)), ?_⟩
  intro P Q a s E D ε m b S hact hS
  obtain ⟨x₀, δ, k, d, hAB, J, hJ, hscale, hδS, hk, hmetric, hcap⟩ := hact
  have hδ0 : 0 < δ := d.precision_pos
  have hδ := hδS.trans hS
  have hδw' : δ ≤ δw := hδ.trans (min_le_left _ _)
  have hδt : δ ≤ (2 * fixed.collarLength + 5 * StandardCap.transitionEnd / 2 + 3)⁻¹ :=
    hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδm : δ ≤ ((m' : ℝ) + 1)⁻¹ := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmk : m' ≤ k := le_order_of_delta_le_C11Q5 hδ0 hδm hk
  obtain ⟨hAB', hfit, hclose⟩ := hwin δ hδ0 hδw'
  have htip := StandardCap.collapseTip_mem_buffer fixed.collar_pos hδ0 hδt
  have hc := hclose k hmk E.terminal.metric x₀ d.oriented
  let w := StandardCap.canonicalStaticInsertionWitness d fixed.collarLength fixed.collar_pos D'
    hD'pos m' ε' hAB' hfit htip hc
  refine ⟨x₀, δ, k, d, w, J ∘ w.window, hJ.comp w.window_smooth (by simp), hscale, ?_, ?_⟩
  · intro x v z
    have hmd : MDifferentiableAt ThreeModel ThreeModel J (w.window x) :=
      hJ.contMDiff.mdifferentiableAt (by simp)
    have hmd' : MDifferentiableAt ThreeModel ThreeModel w.window x :=
      w.window_smooth.contMDiff.mdifferentiableAt (by simp)
    rw [mfderiv_comp_apply x (f := w.window) (g := J) hmd hmd' v,
      mfderiv_comp_apply x (f := w.window) (g := J) hmd hmd' z, ← hscale]
    refine (w.window_inner x v z).trans ?_
    congr 1
    exact hmetric (w.window x) _ _
  · intro z
    obtain ⟨y, hy⟩ := hcap z
    have hyD : ‖y.val‖ < D' + 1 := lt_of_le_of_lt y.2 (by linarith)
    refine ⟨⟨y.val, hyD⟩, y.2, ?_⟩
    change J (StandardCap.modelWindowMap (inv_pos.mpr d.precision_pos) hfit ⟨y.val, hyD⟩) = _
    rw [StandardCap.modelWindowMap_agrees_cap (inv_pos.mpr d.precision_pos) hfit y hyD]
    exact hy

/-- record 的 static cap precision：`S.delta = recenterConstant · δ_α ≤ recenterConstant · δ(t)`。 -/
theorem staticCap_delta_le_C11Q5 {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {params : CutoffParameters} (R : GeometricCutoffRecord H i params)
    (b : (H.event i).RetainedBoundaryIndex) :
    (R.static b).delta ≤ params.recenterConstant * params.delta (H.time i.succ) := by
  rw [R.recenter_delta b]
  exact mul_le_mul_of_nonneg_left (R.delta_le b.1.1) (by linarith [params.recenterConstant_ge_four])

/-- **record 形接口 (3)**：请求 `(D', m', ε')` 的阈值 `δ_*`；record 带实际插入证书且
`recenterConstant · δ(t_event) ≤ δ_*` ⇒ 该 record 每个 static cap 的 fine realization。 -/
theorem fineCapRealization_of_record_C11Q5 (fixed : StaticCapScaffold) (D' : ℝ)
    (hD' : StandardCap.transitionEnd ≤ D') (m' : ℕ) (ε' : ℝ) (hε' : 0 < ε') :
    ∃ δs : ℝ, 0 < δs ∧
      ∀ {H : ObservedHistory.{u}} {i : Fin H.eventCount} {params : CutoffParameters},
        params.fixed = fixed → ∀ (R : GeometricCutoffRecord H i params),
        params.recenterConstant * params.delta (H.time i.succ) ≤ δs →
        ∀ b, ActualCanonicalInsertion_C11Q5 (R.static b) →
          FineCapRealization_C11Q5 (R.static b) D' m' ε' := by
  obtain ⟨δs, hδs, h⟩ := exists_fineCapRealization_of_actual_C11Q5.{u} fixed D' hD' m' ε' hε'
  refine ⟨δs, hδs, ?_⟩
  intro H i params hfixed R hR b hact
  subst hfixed
  exact h (R.static b) hact ((staticCap_delta_le_C11Q5 R b).trans hR)

/-- **consumer**：粗 canonical window 的 records 在自身 model tuple 上已有 fine realization；
带实际插入证书的 records 在任一请求上、δ 足够小时也有。 -/
example {H : ObservedHistory.{u}} {params : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j params)
    (hcanon : ∀ j b, ((records j).static b).hasCanonicalWindow)
    (hact : ∀ j b, ActualCanonicalInsertion_C11Q5 ((records j).static b))
    (D' : ℝ) (hD' : StandardCap.transitionEnd ≤ D') (m' : ℕ) (ε' : ℝ) (hε' : 0 < ε') :
    (∀ j b, FineCapRealization_C11Q5 ((records j).static b) params.modelRadius params.modelOrder
      params.modelAccuracy) ∧
    ∃ δs : ℝ, 0 < δs ∧ ∀ j : Fin H.eventCount,
      params.recenterConstant * params.delta (H.time j.succ) ≤ δs →
      ∀ b, FineCapRealization_C11Q5 ((records j).static b) D' m' ε' := by
  obtain ⟨δs, hδs, h⟩ := fineCapRealization_of_record_C11Q5.{u} params.fixed D' hD' m' ε' hε'
  exact ⟨fun j b => fineCapRealization_of_hasCanonicalWindow_C11Q5 _ (hcanon j b),
    δs, hδs, fun j hj b => h rfl (records j) hj b (hact j b)⟩

end GC.LongTime.Ch11
