import DifferentialGeometry.Geometry.Analytic.ChristoffelBridgeF3A
import DifferentialGeometry.Geometry.Metric.Euclidean

/-!
# F3-a fixture：Euclidean 平坦度量是 analytic metric（O-MY-F3A G2 consumer，后缀 `_F3A`）

`IsAnalyticMetricOn_F3A` 的非空性（inhabitant）：内积空间 `E`（ω-流形，model space）上的
`euclideanMetric` 对 maximal ω-atlas 在任意开集 `P` 上解析。证明只在 `chartAt E x = refl` 下算出常系数
`⟪ξ, η⟫`，再用 G2 的局部判据 `isAnalyticMetricOn_iff_forall_exists_F3A` 换到**所有** ω-chart——
即 chart-independence 的一次真实使用。consumer：树里 `chartChristoffel euclideanMetric p` 的解析性。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Analytic

open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `refl` chart 下平坦度量的系数是常数 `⟪ξ, η⟫`。 -/
theorem metricCoeff_euclideanMetric_refl_F3A (ξ η y : E) :
    metricCoeff_F3A (euclideanMetric (E := E)) (OpenPartialHomeomorph.refl E) ξ η y =
      inner ℝ ξ η := by
  change (euclideanMetric (E := E)).inner y (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (id : E → E) y ξ)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (id : E → E) y η) = _
  rw [mfderiv_id]
  rfl

/-- inhabitant：平坦度量对 maximal ω-atlas 在任意开集 `P` 上解析（经局部判据换到所有 ω-chart）。 -/
theorem isAnalyticMetricOn_euclideanMetric_F3A [FiniteDimensional ℝ E] {P : Set E}
    (hP : IsOpen P) :
    IsAnalyticMetricOn_F3A (IsManifold.maximalAtlas 𝓘(ℝ, E) ω E) P (euclideanMetric (E := E)) := by
  refine (isAnalyticMetricOn_iff_forall_exists_F3A
    (isAnalyticCompatibleAtlas_maximalAtlas_omega_F3A E P) hP).mpr fun x _ => ?_
  refine ⟨chartAt E x, IsManifold.chart_mem_maximalAtlas x, mem_chart_source E x, fun ξ η => ?_⟩
  rw [chartAt_self_eq]
  have hconst : metricCoeff_F3A (euclideanMetric (E := E)) (OpenPartialHomeomorph.refl E) ξ η =
      fun _ => inner ℝ ξ η := funext (metricCoeff_euclideanMetric_refl_F3A ξ η)
  rw [hconst]
  exact analyticAt_const

/-! ## consumer（G2）：树里平坦度量的 `chartChristoffel` 在每个 chart 中解析 -/

example [FiniteDimensional ℝ E] (p : E)
    (i j k : Fin (Module.finrank ℝ E)) :
    AnalyticOnNhd ℝ (chartChristoffel (I := 𝓘(ℝ, E)) (euclideanMetric (E := E)) p i j k)
      ((chartAt E p) '' (univ ∩ (chartAt E p).source)) :=
  analyticOnNhd_chartChristoffel_of_omega_F3A isOpen_univ
    (isAnalyticMetricOn_euclideanMetric_F3A isOpen_univ) p i j k

end DifferentialGeometry.Geometry.Analytic
