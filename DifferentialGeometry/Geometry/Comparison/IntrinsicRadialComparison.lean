import DifferentialGeometry.Geometry.Comparison.IntrinsicBufferComparison
import DifferentialGeometry.Geometry.Comparison.PointOnSideModel
import DifferentialGeometry.Topology.MetricSpace.RadialBall

set_option autoImplicit false

open Set Metric Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (o : X) {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R)
variable [LocallyCompactSpace (ball o (256 * R))]
variable (hlocal : ∀ z : ball o (256 * R), ∃ Ω : Set (ball o (256 * R)),
  @IsOpen (ball o (256 * R))
      (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball o (256 * R))
      (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 256 * R)) κ Ω ∧ z ∈ Ω)

include hcurves hκ hR hlocal

theorem point_on_side_of_intrinsic_256_buffer
    {q u x z : X} (hq : q ∈ ball o (2 * R)) (hu : u ∈ ball o (2 * R))
    (hx : x ∈ ball o (2 * R)) (hz : z ∈ ball o (2 * R))
    (hparts : dist q x = dist q u + dist u x) :
    modelSideNegCurvature κ (dist q u) (dist q z)
      (comparisonAngleNegCurvature κ (dist q x) (dist q z) (dist x z)) ≤ dist u z :=
  modelSideNegCurvature_point_on_side_le_dist hκ
    (fourPointComparison_ambient_two_ball_of_intrinsic_256_buffer hcurves o hκ hR hlocal)
    hq hu hx hz hparts

theorem radial_point_on_side_of_intrinsic_256_buffer
    {q u x z : X} (hq : q ∈ ball o (R / 2))
    (hx : x ∈ closedBall o R) (hz : z ∈ closedBall o R)
    (hparts : dist q x = dist q u + dist u x) :
    modelSideNegCurvature κ (dist q u) (dist q z)
      (comparisonAngleNegCurvature κ (dist q x) (dist q z) (dist x z)) ≤ dist u z := by
  exact point_on_side_of_intrinsic_256_buffer hcurves o hκ hR hlocal
    ((show dist q o < R / 2 from hq).trans_le (by linarith))
    (mem_two_ball_of_radial_between hq hx hparts)
    ((show dist x o ≤ R from hx).trans_lt (by linarith))
    ((show dist z o ≤ R from hz).trans_lt (by linarith)) hparts

theorem independent_radial_monotonicity_of_intrinsic_256_buffer
    {q : X} {A B : ℝ} {γ β : ℝ → X} (hq : q ∈ ball o (R / 2))
    (hγend : γ A ∈ closedBall o R) (hβend : β B ∈ closedBall o R)
    (hγrad : ∀ s ∈ Ioc (0 : ℝ) A, dist q (γ s) = s)
    (hβrad : ∀ t ∈ Ioc (0 : ℝ) B, dist q (β t) = t)
    (hγmin : ∀ s ∈ Ioc (0 : ℝ) A, ∀ t ∈ Ioc (0 : ℝ) A,
      dist (γ s) (γ t) = |s - t|)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) B, ∀ t ∈ Ioc (0 : ℝ) B,
      dist (β s) (β t) = |s - t|) :
    DifferentialGeometry.Toponogov.CoordinatewiseNonincreasingOn A B
      (fun s t => comparisonAngleNegCurvature κ s t (dist (γ s) (β t))) :=
  comparisonAngleNegCurvature_antitone_on_segments hκ
    (fourPointComparison_ambient_two_ball_of_intrinsic_256_buffer hcurves o hκ hR hlocal)
    ((show dist q o < R / 2 from hq).trans_le (by linarith))
    hγrad hβrad hγmin hβmin
    (radial_germ_mem_two_ball hq hγend hγrad hγmin)
    (radial_germ_mem_two_ball hq hβend hβrad hβmin)

end DifferentialGeometry.Geometry.Comparison.Toponogov
