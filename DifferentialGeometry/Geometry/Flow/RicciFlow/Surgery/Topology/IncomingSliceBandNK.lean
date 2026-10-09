import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingNeckBandCylNK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckChartBandNK

/-!
# Route W, c4：surgery 前 slice 的 neck band（S-W-NECK G5，后缀 `_NK`，第 3 部分）

`B : IncomingBackwardNeck H i neck r`（`GeometricCutoffRecord.backward α` 给出）：`τ₀ = H.time i.succ`，
terminal neck `neck : NormalizedNeck (H.event i).terminal.metric δ k` 的 backward 延拓。
`metric_on_slab`（`j = i`）说：`B.metric v = c^*((r²)⁻¹ · g_{τ₀ + r² v})`，其中 `c = B.stageChart i …`
是同一个 stage 的 neck chart，`g_s = (H.event i).incoming.flow.base.metric s`。所以 G2 的
band 估计在 `s ∈ [τ₀ - d, τ₀)` 的 slice `(H.stage i.castSucc).Carrier` 上成立（带余量）：

* `sliceChart_NK`、`sliceHeight_NK`、`sliceMetric_NK s`：chart、高度坐标、`(r²)⁻¹` 归一化的 slice 度量（函数，无新结构）；
* **`slice_band_estimates_NK`**：`∃ d > 0, ∀ s ∈ [τ₀ - d, τ₀)`，五联结论（`range` 开、高度光滑、band 闭包
  在 `range` 内、band 上 `R ≥ 3/5`、`(dz)² ≤ 2 g`）——形状对齐 G2 的 `band_estimates_NK`，
  常数 `3/5 > 1/2`、`2 < 4` 有余量；`slice_band_estimates_half_NK` 是 G2 的 `1/2`、`4` 形式。
证明：圆柱侧 `IncomingBackwardNeck.band_cyl_NK`（`parabolic_closeness` ⇒ 与收缩圆柱 `C²` 接近）+
`chart_band_estimates_NK`（一般嵌入的转运）。
-/

set_option autoImplicit false
noncomputable section

open Set Manifold Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}

/-- neck 的 stage chart（`τ₀ - r² < τ₀`）：`neckBuffer δ → (H.stage i.castSucc).Carrier`。 -/
def IncomingBackwardNeck.sliceChart_NK (B : IncomingBackwardNeck H i neck r) :
    C(neckBuffer δ, (H.stage i.castSucc).Carrier) :=
  B.stageChart i le_rfl (sub_lt_self _ (pow_pos B.radius_pos 2))

/-- 高度坐标 `z : (H.stage i.castSucc).Carrier → ℝ`。 -/
def IncomingBackwardNeck.sliceHeight_NK (B : IncomingBackwardNeck H i neck r) :
    (H.stage i.castSucc).Carrier → ℝ :=
  chartHeight_NK (B.sliceChart_NK : neckBuffer δ → (H.stage i.castSucc).Carrier)

/-- 时刻 `s` 的 slice 度量，`(r²)⁻¹` 归一化。 -/
def IncomingBackwardNeck.sliceMetric_NK (B : IncomingBackwardNeck H i neck r) (s : ℝ) :
    SmoothRiemannianMetric ThreeModel (H.stage i.castSucc).Carrier :=
  scaleMetric (r ^ 2)⁻¹ (inv_pos.mpr (pow_pos B.radius_pos 2))
    ((H.event i).incoming.flow.base.metric s)

/-- **c4：surgery 前 slice 的 neck band 估计（带余量）**。 -/
theorem IncomingBackwardNeck.slice_band_estimates_NK (B : IncomingBackwardNeck H i neck r)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, H.time i.succ - d ≤ s → s < H.time i.succ →
      IsOpen (Set.range B.sliceChart_NK) ∧
      ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ B.sliceHeight_NK (Set.range B.sliceChart_NK) ∧
      closure {p : (H.stage i.castSucc).Carrier |
          p ∈ Set.range B.sliceChart_NK ∧ |B.sliceHeight_NK p| < 20} ⊆
        Set.range B.sliceChart_NK ∧
      (∀ p ∈ Set.range B.sliceChart_NK, |B.sliceHeight_NK p| < 20 →
        3 / 5 ≤ metricScalarAt (B.sliceMetric_NK s) p) ∧
      (∀ p ∈ Set.range B.sliceChart_NK, |B.sliceHeight_NK p| < 20 →
        ∀ w : TangentSpace ThreeModel p,
          (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) B.sliceHeight_NK p w) ^ 2 ≤
            2 * (B.sliceMetric_NK s).inner p w w) := by
  have hr2 : 0 < r ^ 2 := pow_pos B.radius_pos 2
  have hlt : H.time i.castSucc < H.time i.succ := (H.event i).incoming.lt
  refine ⟨min (r ^ 2 / 2) (H.time i.succ - H.time i.castSucc), lt_min (by positivity)
    (by linarith), fun s hs1 hs2 => ?_⟩
  have hs1' : H.time i.succ - r ^ 2 / 2 ≤ s := hs1.trans' (by
    linarith [min_le_left (r ^ 2 / 2) (H.time i.succ - H.time i.castSucc)])
  have hs1'' : H.time i.castSucc ≤ s := hs1.trans' (by
    linarith [min_le_right (r ^ 2 / 2) (H.time i.succ - H.time i.castSucc)])
  set v : ℝ := (s - H.time i.succ) / r ^ 2 with hvdef
  have hv0 : v < 0 := div_neg_of_neg_of_pos (by linarith) hr2
  have hvhalf : -1 / 2 ≤ v := by
    rw [hvdef, le_div_iff₀ hr2]
    linarith
  have hsv : H.time i.succ + r ^ 2 * v = s := by
    have : r ^ 2 * v = s - H.time i.succ := by
      rw [hvdef, mul_div_assoc']
      exact mul_div_cancel_left₀ _ hr2.ne'
    linarith
  have h20 : 20 ≤ δ⁻¹ := by
    have hpos := neck.delta_pos
    rw [le_inv_comm₀ (by norm_num) hpos]
    linarith
  have ha : H.time i.succ - r ^ 2 < H.time i.succ := sub_lt_self _ hr2
  have hslab := B.metric_on_slab i le_rfl ha v ⟨by linarith, hv0⟩ (by rw [hsv]; exact hs1'')
    (by rw [hsv]; exact hs2)
  refine chart_band_estimates_NK (B.stageChart_smooth i le_rfl ha) h20 (B.sliceMetric_NK s)
    (B.metric v) ?_ (a := 3 / 5) (C := 2) ?_ ?_
  · intro x V W
    change _ = (scaleMetric _ _ _).inner _ _ _
    rw [scaleMetric_inner, hslab x V W, hsv]
  · intro x hx
    exact (B.band_cyl_NK hk hδ v ⟨hvhalf, hv0.le⟩ x (abs_le.mp (hx.le.trans h20))).1
  · intro x hx w
    exact (B.band_cyl_NK hk hδ v ⟨hvhalf, hv0.le⟩ x (abs_le.mp (hx.le.trans h20))).2 w

/-- G2 的 `1/2`、`4` 形式（弱化）。 -/
theorem IncomingBackwardNeck.slice_band_estimates_half_NK (B : IncomingBackwardNeck H i neck r)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, H.time i.succ - d ≤ s → s < H.time i.succ →
      IsOpen (Set.range B.sliceChart_NK) ∧
      ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ B.sliceHeight_NK (Set.range B.sliceChart_NK) ∧
      closure {p : (H.stage i.castSucc).Carrier |
          p ∈ Set.range B.sliceChart_NK ∧ |B.sliceHeight_NK p| < 20} ⊆
        Set.range B.sliceChart_NK ∧
      (∀ p ∈ Set.range B.sliceChart_NK, |B.sliceHeight_NK p| < 20 →
        1 / 2 ≤ metricScalarAt (B.sliceMetric_NK s) p) ∧
      (∀ p ∈ Set.range B.sliceChart_NK, |B.sliceHeight_NK p| < 20 →
        ∀ w : TangentSpace ThreeModel p,
          (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) B.sliceHeight_NK p w) ^ 2 ≤
            4 * (B.sliceMetric_NK s).inner p w w) := by
  obtain ⟨d, hd, h⟩ := B.slice_band_estimates_NK hk hδ
  refine ⟨d, hd, fun s hs1 hs2 => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h s hs1 hs2
  refine ⟨h1, h2, h3, fun p hp hz => (by norm_num : (1 : ℝ) / 2 ≤ 3 / 5).trans (h4 p hp hz),
    fun p hp hz w => ?_⟩
  have := h5 p hp hz w
  have h0 := metric_inner_self_nonneg (B.sliceMetric_NK s) p w
  linarith

/-- `GeometricCutoffRecord.order_lower` 给 `k ≥ 2`（实际 `≥ 6`），所以 G5 对 record 的 `backward α`
只剩 `δ ≤ 1/40000` 一个条件（`delta_le` + 晚期 `δ(t)` 小）。 -/
theorem GeometricCutoffRecord.two_le_order_NK {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) (α : (H.event i).transition.trace.tubes.Index) :
    2 ≤ R.order α :=
  (by omega : 2 ≤ p.modelOrder + 6).trans ((le_max_left _ _).trans (R.order_lower α))

/-- consumer：record 的 `backward α` 上 G5 的 `slice_band_estimates_half_NK` 直接适用（型对齐）。 -/
example {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (α : (H.event i).transition.trace.tubes.Index) (hδ : R.delta α ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, H.time i.succ - d ≤ s → s < H.time i.succ →
      IsOpen (Set.range (R.backward α).sliceChart_NK) := by
  obtain ⟨d, hd, h⟩ := (R.backward α).slice_band_estimates_half_NK (R.two_le_order_NK α) hδ
  exact ⟨d, hd, fun s h1 h2 => (h s h1 h2).1⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
