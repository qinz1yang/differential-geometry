import DifferentialGeometry.Geometry.Metric.Scaling.RiemannianBalls
import DifferentialGeometry.Geometry.Metric.Conformal
namespace GC.MetricGeometry
open DifferentialGeometry
noncomputable section

abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)
def euclideanThreeMetric := Geometry.euclideanMetric ThreeSpace

theorem euclideanThree_unit_normalization :
    riemannianClosedBallOf (scaleMetric (((2 : ℝ)⁻¹)^2)
      (sq_pos_of_pos (inv_pos.mpr (by norm_num : (0 : ℝ) < 2))) euclideanThreeMetric)
        (0 : ThreeSpace) 1 =
      riemannianClosedBallOf euclideanThreeMetric (0 : ThreeSpace) 2 :=
  normalized_closedBall euclideanThreeMetric 0 2 (by norm_num)

theorem euclideanThree_buffer :
    riemannianClosedBallOf (scaleMetric (((2 : ℝ)⁻¹)^2)
      (sq_pos_of_pos (inv_pos.mpr (by norm_num : (0 : ℝ) < 2))) euclideanThreeMetric)
        (0 : ThreeSpace) 3 ⊆
      riemannianClosedBallOf euclideanThreeMetric (0 : ThreeSpace) 8 := by
  simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using normalized_buffer_inclusion euclideanThreeMetric 0 2 (by norm_num)
    (R := 3) (S := 4) (by norm_num)

end
end GC.MetricGeometry
