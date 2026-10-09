import DifferentialGeometry.Geometry.Metric.Approximation.RealBallExamples
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.SeamExamples

namespace GC.MetricGeometry
open PointedBallApprox

theorem realRestriction_covers_closed_endpoint :
    ∃ x : BallCarrier (0 : ℝ) 3, dist (1 : ℝ) (realRestriction.toFun x) < 2 :=
  realRestriction.coverage 1 (by norm_num [Real.dist_eq])

end GC.MetricGeometry

namespace GC.Topology

theorem twoLoop_seam_fiber (i : Fin 2) :
    {s : ExampleSide | twoLoopSides.seam s = twoLoopSides.seam (i, false)} =
      {(i, false), (i, true)} := by
  simpa [twoLoopSides] using twoLoopSides.seam_fiber (i, false)

theorem twoLoop_geometry_with_exact_labels :
    (∀ i : Fin 2,
      {s : ExampleSide | twoLoopSides.seam s = twoLoopSides.seam (i, false)} =
        {(i, false), (i, true)}) ∧
    Disjoint (actualSeamImage (twoLoopSides.seam (0, false)))
      (actualSeamImage (twoLoopSides.seam (1, false))) :=
  ⟨twoLoop_seam_fiber, actual_seams_disjoint⟩

end GC.Topology
