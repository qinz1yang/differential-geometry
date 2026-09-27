import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem eventually_extChartAt_symm_mem_chartAt_source (α : M) :
    ∀ᶠ y in 𝓝 (extChartAt I α α), (extChartAt I α).symm y ∈ (chartAt H α).source := by
  have hmem : (chartAt H α) α ∈ (chartAt H α).target :=
    (chartAt H α).map_source (mem_chart_source H α)
  have hval : I.invFun (extChartAt I α α) = (chartAt H α) α := by
    rw [extChartAt_coe, Function.comp_apply]
    exact ModelWithCorners.left_inv I ((chartAt H α) α)
  have ht : (chartAt H α).target ∈ 𝓝 (I.invFun (extChartAt I α α)) := by
    rw [hval]
    exact (chartAt H α).open_target.mem_nhds hmem
  have hev : ∀ᶠ y in 𝓝 (extChartAt I α α), I.invFun y ∈ (chartAt H α).target :=
    I.continuous_invFun.continuousAt.eventually ht
  filter_upwards [hev] with y hy
  rw [extChartAt_coe_symm, Function.comp_apply]
  exact (chartAt H α).map_target hy

end DifferentialGeometry
