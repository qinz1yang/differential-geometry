import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Proper
import DifferentialGeometry.Geometry.Metric.Distance.Ball

universe u uE uH

section

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth

theorem ProperMetricOn.riemannianClosedBallOf_eq_closedBall
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (P : ProperMetricOn Y) (x : Y.M) {r : ℝ} (hr : 0 ≤ r) :
    riemannianClosedBallOf Y.metric x r =
      (letI : MetricSpace Y.M := P.ms; Metric.closedBall x r) := by
  ext y
  have hreal : riemannianEDistOf Y.metric x y =
      ENNReal.ofReal (letI : MetricSpace Y.M := P.ms; dist x y) :=
    P.realizes x y
  change riemannianEDistOf Y.metric x y ≤ ENNReal.ofReal r ↔
    (letI : MetricSpace Y.M := P.ms; dist y x) ≤ r
  rw [hreal, ENNReal.ofReal_le_ofReal_iff hr]
  let : MetricSpace Y.M := P.ms
  rw [dist_comm]

theorem ProperMetricOn.riemannianBallOf_eq_ball
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (P : ProperMetricOn Y) (x : Y.M) (r : ℝ) :
    riemannianBallOf Y.metric x r =
      (letI : MetricSpace Y.M := P.ms; Metric.ball x r) := by
  ext y
  have hreal : riemannianEDistOf Y.metric x y =
      ENNReal.ofReal (letI : MetricSpace Y.M := P.ms; dist x y) :=
    P.realizes x y
  change riemannianEDistOf Y.metric x y < ENNReal.ofReal r ↔
    (letI : MetricSpace Y.M := P.ms; dist y x) < r
  rw [hreal]
  let : MetricSpace Y.M := P.ms
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg, dist_comm]

end DifferentialGeometry.CheegerGromovCompactness

end
