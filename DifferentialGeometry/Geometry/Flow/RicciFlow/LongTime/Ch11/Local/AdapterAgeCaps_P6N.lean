import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeObject_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonMetric
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

/-!
# G3b（AD-age）：static cap witness 的抛物重标度（`_P6N`，records 的 `static` 字段前半）

`StaticCapWitness.rescale_P6N`：neck 换成 `neck.rescale_P6N μ`（`h ↦ μ⁻¹ h`）时，witness 的
`metric`、`retainedMetric` 同乘 `μ⁻¹`；`windowMetric`（已按 `neck.scale` 归一化）不变；
`collapse_locallyLipschitz` 两侧 edist 同乘 `√μ⁻¹`（树内 `edistOf_scale`）、`collapse_length` 两侧长度同乘
`√μ⁻¹`（`riemannianCurveLength_scaleMetric`）；其余（拓扑 / chart / 标准帽窗口 / 径向函数）照搬。
`castWitness_P6N`：沿 terminal open 相等搬到 `castNeck_P6N` 上（供 `PresentedStaticCap` 重标度）。
-/

set_option autoImplicit false

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Witness

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **`_P6N`**：static cap witness 的抛物重标度（见文件头）。 -/
def StaticCapWitness.rescale_P6N {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
    {neck : NormalizedNeck h δ k} {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}
    (W : StaticCapWitness neck fixed D m ε) (μ : ℝ) (hμ : 0 < μ) :
    StaticCapWitness (neck.rescale_P6N μ hμ) fixed D m ε :=
  { W with
    metric := scaleMetric μ⁻¹ (inv_pos.mpr hμ) W.metric
    retainedMetric := by
      letI := W.retainedCharts
      letI := W.retainedSmooth
      exact scaleMetric μ⁻¹ (inv_pos.mpr hμ) W.retainedMetric
    retained_metric_output := by
      let _ := W.retainedCharts
      let _ := W.retainedSmooth
      intro x V U
      change μ⁻¹ * W.retainedMetric.inner x V U = μ⁻¹ * _
      rw [W.retained_metric_output x V U]
      rfl
    retained_metric_input := by
      let _ := W.retainedCharts
      let _ := W.retainedSmooth
      intro x V U
      change μ⁻¹ * W.retainedMetric.inner x V U = μ⁻¹ * _
      rw [W.retained_metric_input x V U]
      rfl
    window_inner := by
      intro x V U
      rw [W.window_inner x V U, scaleMetric_inner]
      change neck.scale * _ = μ * neck.scale * (μ⁻¹ * _)
      field_simp
    collapse_locallyLipschitz := by
      intro x
      obtain ⟨U, hU, L, hL⟩ := W.collapse_locallyLipschitz x
      refine ⟨U, hU, L, fun y hy z hz => ?_⟩
      rw [edistOf_scale, edistOf_scale]
      calc ENNReal.ofReal (Real.sqrt μ⁻¹) *
            riemannianEDistOf W.metric (W.collapse y) (W.collapse z)
          ≤ ENNReal.ofReal (Real.sqrt μ⁻¹) *
            (L * riemannianEDistOf h (neck.chart y.1) (neck.chart z.1)) := by
            gcongr
            exact hL y hy z hz
        _ = L * (ENNReal.ofReal (Real.sqrt μ⁻¹) *
            riemannianEDistOf h (neck.chart y.1) (neck.chart z.1)) := by ring
    collapse_length := by
      intro γ a b hab hγ hfin
      rw [riemannianCurveLength_scaleMetric] at hfin ⊢
      rw [riemannianCurveLength_scaleMetric]
      have hfin' : ENNReal.ofReal (Real.sqrt μ⁻¹) *
          riemannianCurveLength h (fun t => neck.chart (γ t).1) a b ≠ ⊤ := hfin
      have hne : riemannianCurveLength h (fun t => neck.chart (γ t).1) a b ≠ ⊤ := by
        intro htop
        apply hfin'
        rw [htop]
        exact ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (inv_pos.mpr hμ))).ne'
      gcongr
      exact W.collapse_length γ a b hab hγ hne }

/-- consumer：重标度 witness 的标准帽窗口度量（`neck.scale` 归一化）不变、输出度量乘 `μ⁻¹`——即
`hasCanonicalWindow` 的 `windowMetric` 条款与 `PresentedStaticCap.inclusion_metric` 的 `μ⁻¹` 两侧相消所需的形。 -/
example {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ} {neck : NormalizedNeck h δ k}
    {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ} (W : StaticCapWitness neck fixed D m ε)
    (μ : ℝ) (hμ : 0 < μ) :
    (W.rescale_P6N μ hμ).windowMetric = W.windowMetric ∧
      (W.rescale_P6N μ hμ).metric = scaleMetric μ⁻¹ (inv_pos.mpr hμ) W.metric ∧
      (neck.rescale_P6N μ hμ).scale = μ * neck.scale :=
  ⟨rfl, rfl, rfl⟩

end Witness

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
