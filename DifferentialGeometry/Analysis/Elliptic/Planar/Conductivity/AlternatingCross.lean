import DifferentialGeometry.Analysis.Elliptic.Euclidean.DivergenceMaximumPrinciple
import DifferentialGeometry.Topology.PlanarJordan.DiskAlternatingCross

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Topology.PlanarJordan

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem IsSolution.not_local_alternating_cross_of_coordinate_boundary
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hv : ContDiffOn ℝ 2 v (Metric.ball (0 : V) R))
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v)
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x 0)
    (e : OpenPartialHomeomorph (ℝ × ℝ) V)
    (he : (0 : ℝ × ℝ) ∈ e.source) (heR : e (0, 0) ∈ Metric.ball (0 : V) R)
    {η : ℝ} (hη : 0 < η)
    (hpositive : ∀ t : ℝ, 0 < |t| → |t| < η → v (e (0, 0)) < v (e (t, 0)))
    (hnegative : ∀ t : ℝ, 0 < |t| → |t| < η → v (e (0, t)) < v (e (0, 0))) : False := by
  apply not_local_alternating_cross_of_disk_maximum_minimum_principle hR hc hbd
    (fun S hS _ hsub a hfront => ?_) (fun S hS _ hsub a hfront => ?_)
    e he heR hη hpositive hnegative
  · apply hu.le_on_relatively_open_closedBall_of_le_frontier hR B hAB hv hc huv hS
      (fun x hx => ?_) hfront
    have hne : ‖(x : V)‖ ≠ R := hsub hx
    have hle : ‖(x : V)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    simpa using lt_of_le_of_ne hle hne
  · apply hu.le_on_relatively_open_closedBall_of_frontier_le hR B hAB hv hc huv hS
      (fun x hx => ?_) hfront
    have hne : ‖(x : V)‖ ≠ R := hsub hx
    have hle : ‖(x : V)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    simpa using lt_of_le_of_ne hle hne

end DeGiorgi

end

end
