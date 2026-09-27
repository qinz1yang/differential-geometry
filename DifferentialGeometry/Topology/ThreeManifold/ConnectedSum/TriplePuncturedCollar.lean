import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TriplePunctured

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.BallChart

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] (e c d : BallChart 3 (𝓡 3) M)
  (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
  (hed : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))

def tripleRadialFirst (z : S2) (r : ℝ) (hr : r ∈ Icc 1 2) : e.TriplePunctured c d := by
  have hmem : e.chart (r • z.val) ∈ e.chart '' Metric.closedBall 0 2 :=
    ⟨r • z.val, by rw [Metric.mem_closedBall, dist_zero_right, norm_radial z (by linarith [hr.1])]; exact hr.2, rfl⟩
  exact ⟨e.chart (r • z.val), (e.radialMap z r hr).property,
    fun h => Set.disjoint_left.mp hec hmem (Set.image_mono
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))) h),
    fun h => Set.disjoint_left.mp hed hmem (Set.image_mono
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))) h)⟩

theorem tripleRadialFirst_val (z : S2) (r : ℝ) (hr : r ∈ Icc 1 2) :
    (tripleRadialFirst e c d hec hed z r hr).val = e.chart (r • z.val) := rfl

theorem tripleToFirst_tripleRadialFirst (z : S2) (r : ℝ) (hr : r ∈ Icc 1 2) :
    tripleToFirst e c d (tripleRadialFirst e c d hec hed z r hr) = e.radialMap z r hr := rfl

end DifferentialGeometry.Topology.BallChart
