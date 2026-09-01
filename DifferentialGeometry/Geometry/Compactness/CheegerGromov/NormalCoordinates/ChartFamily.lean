import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.MetricBounds
import DifferentialGeometry.Geometry.Comparison.NormalCoordinateSmoothness
import DifferentialGeometry.Geometry.Exponential.NormalBallChart

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]

section ControlledNormalCharts

variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

abbrev NormalChartAt
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) : Type (max u uE) :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  NormalBallChart (I := I) x

abbrev NormalChartFamily
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :=
  ∀ (k : Nat) (x : (X.obj k).M),
    NormalChartAt (I := I) (X.obj k) x

namespace NormalChartFamily

def radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X) (k : Nat)
    (x : (X.obj k).M) : Real :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (chart k x).radius

def hom
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X) (k : Nat)
    (x : (X.obj k).M) : E → (X.obj k).M :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (chart k x).hom

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X) (f : Nat → Nat) :
    NormalChartFamily (I := I) (X.subseq f) :=
  fun k x => chart (f k) x

def transition
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X) (k : Nat)
    (x y : (X.obj k).M) : E → E :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (chart k x).transition (chart k y)

noncomputable def metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X) (k : Nat)
    (x : (X.obj k).M) : E → (E →L[Real] E →L[Real] Real) :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (chart k x).metric (X.obj k).metric

end NormalChartFamily

noncomputable def c2RadiusNormalBallChart
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    NormalBallChart (I := I) x := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let U := Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)
  have hsub : U ⊆ (expMapDiffeo (I := I) Y.metric x).source := by
    intro z hz
    apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x
    simpa only [U, Metric.mem_ball, dist_zero_right] using hz
  have himage :
      (fun z => expMapDiffeo (I := I) Y.metric x z) '' U =
        (fun z : E => (expMap (I := I) Y.metric x
          (show TangentSpace I x from z) : Y.M)) '' U := by
    apply Set.image_congr
    intro z hz
    exact expMapDiffeo_apply_eq (I := I) Y.metric x (hsub hz)
  exact
    { radius := expMapC2Radius (I := I) Y.metric x
      radius_pos := expMapC2Radius_pos (I := I) Y.metric x
      hom := expMapDiffeo (I := I) Y.metric x
      ball_subset := hsub
      map_zero := expMapDiffeo_zero (I := I) Y.metric x
      smooth_to := exp_map_diffeo_cont_mdiff_on_exp_ball (I := I) Y x
      smooth_inv := by
        rw [himage]
        exact normal_chart_at_cont_mdiff_on_infty (I := I) Y.metric x }

noncomputable def c2RadiusNormalChartFamily
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    NormalChartFamily (I := I) X :=
  fun k x => c2RadiusNormalBallChart (I := I) (X.obj k) x

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem c2_radius_normal_ball_chart_radius
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).radius =
      expMapC2Radius (I := I) Y.metric x :=
  rfl

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem c2_radius_normal_ball_chart_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) (z : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).hom z =
      expMapDiffeo (I := I) Y.metric x z := by
  rfl

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem c2_radius_normal_ball_chart_inv
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).inv =
      normalChartAt (I := I) Y.metric x := by
  rfl

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem c2_radius_normal_ball_chart_target
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).hom.target =
      (normalChartAt (I := I) Y.metric x).source := by
  rfl

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_image
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).hom ''
        Metric.ball (0 : E) (c2RadiusNormalBallChart (I := I) Y x).radius =
      (fun z : E => (expMap (I := I) Y.metric x (show TangentSpace I x from z) : Y.M)) ''
        Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [c2_radius_normal_ball_chart_radius]
  apply Set.image_congr
  intro z hz
  rw [c2_radius_normal_ball_chart_apply]
  exact expMapDiffeo_apply_eq (I := I) Y.metric x
    ((c2RadiusNormalBallChart (I := I) Y x).ball_subset hz)

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_metric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).metric Y.metric =
    normalCoordMetric (I := I) Y x := by
  rfl

def NormalCoordMetricBounds.metricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (c2RadiusNormalBallChart (I := I) (X.obj k) x).MetricBounds
      (X.obj k).metric := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  exact
    { C := h.metricC
      C_nonneg := h.metricC_nonneg
      radius := h.radius k x
      radius_pos := h.radius_pos k x
      equiv := by
        simpa only [NormalBallChart.MetricEquivOn, NormalCoordMetricEquivOn,
          c2_radius_normal_ball_chart_metric] using
          h.metric_equiv k x
      deriv := fun p => by
        simpa only [NormalBallChart.MetricDerivBound, NormalCoordMetricDerivBound,
          c2_radius_normal_ball_chart_metric] using
          h.metric_deriv k p x }

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_transition
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x y : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).transition
        (c2RadiusNormalBallChart (I := I) Y y) =
      normalTransition (I := I) Y x y := by
  rfl

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_overlap_iff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x y : Y.M) (U : Set E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).OverlapOn
        (c2RadiusNormalBallChart (I := I) Y y) U ↔
      ∀ z ∈ U,
        z ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x) ∧
        expMapDiffeo (I := I) Y.metric x z ∈
          (fun z : E => (expMap (I := I) Y.metric y (show TangentSpace I y from z) : Y.M)) ''
            Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric y) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [NormalBallChart.OverlapOn, c2_radius_normal_ball_chart_radius,
    c2_radius_normal_ball_chart_image]
  simp only [c2_radius_normal_ball_chart_apply]

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_metric_equiv_iff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) (U : Set E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).MetricEquivOn Y.metric U ↔
      NormalCoordMetricEquivOn (I := I) Y x U := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [NormalBallChart.MetricEquivOn, NormalCoordMetricEquivOn,
    c2_radius_normal_ball_chart_metric (I := I)]

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_metric_deriv_iff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) (U : Set E) (p : Nat) (C : Real) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).MetricDerivBound
        Y.metric U p C ↔
      NormalCoordMetricDerivBound (I := I) Y x U p C := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [NormalBallChart.MetricDerivBound, NormalCoordMetricDerivBound,
    c2_radius_normal_ball_chart_metric (I := I)]

end ControlledNormalCharts

end HCGCompactness
end DifferentialGeometry
