import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.MetricSpace.ProperSpace


open Set Metric
open scoped Topology

namespace DifferentialGeometry.Topology.Manifold

theorem exists_extChartAt_symm_image_closedBall_subset
    {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    [TopologicalSpace M] [ChartedSpace H M]
    (a : M) {W : Set E} {z : E} (hW : W ∈ 𝓝 z)
    (hWt : W ⊆ (extChartAt I a).target) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ W ∧
      IsCompact ((extChartAt I a).symm '' closedBall z r) ∧
      (extChartAt I a).symm '' closedBall z r ⊆ (extChartAt I a).source ∧
      ball z r ⊆ extChartAt I a '' ((extChartAt I a).symm '' closedBall z r) := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hW
  have htarget : closedBall z r ⊆ (extChartAt I a).target := hsub.trans hWt
  refine ⟨r, hr, hsub, ?_, ?_, ?_⟩
  · exact (isCompact_closedBall z r).image_of_continuousOn
      ((continuousOn_extChartAt_symm a).mono htarget)
  · rintro x ⟨y, hy, rfl⟩
    exact (extChartAt I a).map_target (htarget hy)
  · rw [(extChartAt I a).image_symm_image_of_subset_target htarget]
    exact ball_subset_closedBall

end DifferentialGeometry.Topology.Manifold
