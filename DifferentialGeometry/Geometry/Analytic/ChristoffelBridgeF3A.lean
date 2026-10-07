import DifferentialGeometry.Geometry.Analytic.ChristoffelF3A
import DifferentialGeometry.Geometry.Connection.ChartBridge.Connection.Christoffel

/-!
# F3-a：`christoffel_F3A` 与树里 `chartChristoffel` 的对齐（O-MY-F3A G2c，后缀 `_F3A`）

树里 harmonic map 的 chart 方程（`diskMapTension_eq_zero_of_chart_laplacian`，
`Geometry/HarmonicMap/ChartTension.lean`）用的是 `Operator.chartChristoffel g p`（`extChartAt` 版、
basis `chartModelBasis E`）。本文件证明在 `(chartAt E p).target` 上它与 `christoffel_F3A g (chartAt E p)
(chartModelBasis E)` 逐点相等，于是 R8-AR 可以直接拿到**树里那个** `Γ` 的 analytic 性：
- `chartAt E p ∈ 𝒜`（compatible atlas）且 `G` 对 `𝒜` 解析 ⇒ `chartChristoffel G p i j k` analytic；
- ω-流形：`G` 对 maximal ω-atlas 解析 ⇒ 对每个 `p` 都成立（`chartAt E p` 在 maximal ω-atlas 里）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Analytic

open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Geometry.Operator

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 树里的 chart frame `chartBasisVecFiber p i` 在 `(chartAt E p).symm y` 处
= `D((chartAt E p).symm)_y (b i)`。 -/
theorem chartBasisVecFiber_eq_mfderiv_F3A (p : M) {y : E} (hy : y ∈ (chartAt E p).target)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := 𝓘(ℝ, E)) p i ((chartAt E p).symm y) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y (chartModelBasis E i) := by
  have hx : (chartAt E p).symm y ∈ (chartAt E p).source := (chartAt E p).map_target hy
  rw [chartBasisVecFiber, TangentBundle.symmL_trivializationAt hx]
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ]
  rw [show extChartAt 𝓘(ℝ, E) p ((chartAt E p).symm y) = y from (chartAt E p).right_inv hy]
  rfl

/-- 树里的 `chartGramOnE g p i j` 在 `(chartAt E p).target` 上
= `metricCoeff_F3A g (chartAt E p) (b i) (b j)`。 -/
theorem chartGramOnE_eq_metricCoeff_F3A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := 𝓘(ℝ, E)) g p i j y =
      metricCoeff_F3A g (chartAt E p) (chartModelBasis E i) (chartModelBasis E j) y := by
  rw [chartGramOnE_def, chartGramMatrix_apply]
  change g.inner ((chartAt E p).symm y)
      (chartBasisVecFiber (I := 𝓘(ℝ, E)) p i ((chartAt E p).symm y))
      (chartBasisVecFiber (I := 𝓘(ℝ, E)) p j ((chartAt E p).symm y)) = _
  rw [chartBasisVecFiber_eq_mfderiv_F3A p hy, chartBasisVecFiber_eq_mfderiv_F3A p hy]
  rfl

/-- 对齐：在 `(chartAt E p).target` 上
`chartChristoffel g p = christoffel_F3A g (chartAt E p) (chartModelBasis E)`。 -/
theorem chartChristoffel_eq_christoffel_F3A
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) {y : E} (hy : y ∈ (chartAt E p).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := 𝓘(ℝ, E)) g p i j k y =
      christoffel_F3A g (chartAt E p) (chartModelBasis E) i j k y := by
  have hgram : chartInvGramMatrix (I := 𝓘(ℝ, E)) g p ((extChartAt 𝓘(ℝ, E) p).symm y) =
      (metricGram_F3A g (chartAt E p) (chartModelBasis E) y)⁻¹ := by
    unfold chartInvGramMatrix
    congr 1
    ext a c
    exact chartGramOnE_eq_metricCoeff_F3A g p hy a c
  have hpd : ∀ a c d : Fin (Module.finrank ℝ E),
      partialDeriv d (chartGramOnE (I := 𝓘(ℝ, E)) g p a c) y =
        fderiv ℝ (metricCoeff_F3A g (chartAt E p) (chartModelBasis E a) (chartModelBasis E c))
          y (chartModelBasis E d) := by
    intro a c d
    have heq : chartGramOnE (I := 𝓘(ℝ, E)) g p a c =ᶠ[𝓝 y]
        metricCoeff_F3A g (chartAt E p) (chartModelBasis E a) (chartModelBasis E c) := by
      filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
      exact chartGramOnE_eq_metricCoeff_F3A g p hz a c
    rw [partialDeriv, heq.fderiv_eq]
  rw [chartChristoffel_def, christoffel_F3A, hgram]
  simp only [hpd]

/-- R8-AR 的 analytic `Γ`（树里那个）：`G` 对 compatible atlas 解析、`chartAt E p ∈ 𝒜` ⇒
`chartChristoffel G p i j k` 在 `(chartAt E p) '' (P ∩ source)` 上 `AnalyticOnNhd`。 -/
theorem IsAnalyticMetricOn_F3A.analyticOnNhd_chartChristoffel
    {𝒜 : Set (OpenPartialHomeomorph M E)} {P : Set M} {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : IsAnalyticMetricOn_F3A 𝒜 P G) (hP : IsOpen P)
    (h𝒜 : ∀ e ∈ 𝒜, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {p : M} (hp : chartAt E p ∈ 𝒜)
    (i j k : Fin (Module.finrank ℝ E)) :
    AnalyticOnNhd ℝ (chartChristoffel (I := 𝓘(ℝ, E)) G p i j k)
      ((chartAt E p) '' (P ∩ (chartAt E p).source)) := by
  have hopen : IsOpen ((chartAt E p) '' (P ∩ (chartAt E p).source)) :=
    (chartAt E p).isOpen_image_of_subset_source (hP.inter (chartAt E p).open_source)
      inter_subset_right
  refine (hG.analyticOnNhd_christoffel hP h𝒜 hp (chartModelBasis E) i j k).congr hopen ?_
  rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
  exact (chartChristoffel_eq_christoffel_F3A G p ((chartAt E p).map_source hx) i j k).symm

/-- ω-流形版：`G` 对 maximal ω-atlas 在 `P` 上解析 ⇒ 对**每个** `p`，树里的 `chartChristoffel G p`
在 `(chartAt E p) '' (P ∩ source)` 上解析。 -/
theorem analyticOnNhd_chartChristoffel_of_omega_F3A [IsManifold 𝓘(ℝ, E) ω M]
    {P : Set M} (hP : IsOpen P)
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : IsAnalyticMetricOn_F3A (IsManifold.maximalAtlas 𝓘(ℝ, E) ω M) P G) (p : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    AnalyticOnNhd ℝ (chartChristoffel (I := 𝓘(ℝ, E)) G p i j k)
      ((chartAt E p) '' (P ∩ (chartAt E p).source)) :=
  hG.analyticOnNhd_chartChristoffel hP
    (isAnalyticCompatibleAtlas_maximalAtlas_omega_F3A M P).mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas p) i j k

end DifferentialGeometry.Geometry.Analytic
