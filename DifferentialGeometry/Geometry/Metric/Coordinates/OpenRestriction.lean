import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Bundle.TangentOpenRestriction

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chartBasisVec_open
    (U : Opens M) (a x : U)
    (hx : (x : M) ∈ (chartAt H (a : M)).source)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) a i x = chartBasisVecFiber (I := I) (a : M) i (x : M) := by
  let _ : Nonempty U := ⟨a⟩
  have hxU : x ∈ (chartAt H a).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hx
  change (trivializationAt E (TangentSpace I (M := U)) a).symmL ℝ x (chartModelBasis E i) =
    (trivializationAt E (TangentSpace I (M := M)) (a : M)).symmL ℝ (x : M) (chartModelBasis E i)
  rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) hxU,
    TangentBundle.symmL_trivializationAt_eq_core (I := I) hx,
    tangentCoordChange_opens (I := I) a x x hx]
  rfl

theorem chartGramMatrix_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : Opens M) [T2Space U] (a x : U)
    (hx : (x : M) ∈ (chartAt H (a : M)).source)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (g.restrictOpen U) a x i j = chartGramMatrix g (a : M) (x : M) i j := by
  rw [chartGramMatrix_apply, chartGramMatrix_apply, SmoothRiemannianMetric.restrictOpen_inner,
    chartBasisVec_open U a x hx i, chartBasisVec_open U a x hx j]

end DifferentialGeometry.Tensor.Coordinates

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartGramOnE_eventuallyEq_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : Opens M) [T2Space U] (a : U)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (g.restrictOpen U) a i j =ᶠ[𝓝 (extChartAt I a a)]
      chartGramOnE g (a : M) i j := by
  let _ : Nonempty U := ⟨a⟩
  filter_upwards [extChartAt_target_mem_nhds (I := I) a] with y hy
  change chartGramMatrix (g.restrictOpen U) a ((extChartAt I a).symm y) i j =
    chartGramMatrix g (a : M) ((extChartAt I (a : M)).symm y) i j
  have hzU : (extChartAt I a).symm y ∈ (extChartAt I a).source :=
    (extChartAt I a).map_target hy
  have hzM : (((extChartAt I a).symm y : U) : M) ∈
      (chartAt H (a : M)).source := by
    rw [extChartAt_source, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source] at hzU
    exact hzU
  have hval : (((extChartAt I a).symm y : U) : M) =
      (extChartAt I (a : M)).symm y := by
    have hyTarget : I.symm y ∈ (chartAt H a).target := by
      have hy' : (∃ z, I z = y) ∧ I.symm y ∈ (chartAt H a).target := by
        simpa [extChartAt] using hy
      exact hy'.2
    change ((chartAt H a).symm (I.symm y) : U) =
      (chartAt H (a : M)).symm (I.symm y)
    rw [TopologicalSpace.Opens.chartAt_eq] at hyTarget ⊢
    exact OpenPartialHomeomorph.subtypeRestr_symm_apply _ _ hyTarget
  rw [← hval]
  exact chartGramMatrix_restrictOpen g U a ((extChartAt I a).symm y) hzM i j

end DifferentialGeometry.Geometry.Operator
