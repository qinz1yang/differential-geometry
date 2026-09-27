import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Framed

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

local instance framedBoundsFormNormedAddCommGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance framedBoundsFormNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)] H I in
theorem metricEquivOn_ball_of_norm_fderiv_le_innerSL
    {F : E → E →L[Real] E →L[Real] Real} {s C : Real} (hs : 0 < s) (hC : 0 ≤ C)
    (hzero : F 0 = (innerSL Real : E →L[Real] E →L[Real] Real))
    (hdiff : ∀ z ∈ Metric.ball (0 : E) s, DifferentiableAt Real F z)
    (hderiv : ∀ z ∈ Metric.ball (0 : E) s, ‖fderiv Real F z‖ ≤ C) :
    ∀ z ∈ Metric.ball (0 : E) (min s (1 / (2 * C + 1))), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ F z v v ∧ F z v v ≤ 2 * ‖v‖ ^ 2 := by
  have hden : 0 < 2 * C + 1 := by linarith
  have h0 : (0 : E) ∈ Metric.ball (0 : E) s := Metric.mem_ball_self hs
  intro z hz v
  have hzs : z ∈ Metric.ball (0 : E) s :=
    Metric.ball_subset_ball (min_le_left _ _) hz
  have hzr : ‖z‖ ≤ 1 / (2 * C + 1) := by
    have h := Metric.mem_ball.mp hz
    rw [dist_zero_right] at h
    exact le_of_lt (lt_of_lt_of_le h (min_le_right _ _))
  have hnorm : ‖F z - F 0‖ ≤ C * ‖z‖ := by
    have hmean := (convex_ball (0 : E) s).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := Real) hdiff hderiv h0 hzs
    rw [sub_zero] at hmean
    exact hmean
  have hdist : ‖F z - F 0‖ ≤ 1 / 2 := by
    calc ‖F z - F 0‖ ≤ C * ‖z‖ := hnorm
      _ ≤ C * (1 / (2 * C + 1)) := mul_le_mul_of_nonneg_left hzr hC
      _ ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hden]
        nlinarith
  have h0vv : F 0 v v = ‖v‖ ^ 2 := by
    rw [hzero, innerSL_apply_apply, real_inner_self_eq_norm_sq]
  have hbound : |F z v v - ‖v‖ ^ 2| ≤ (1 / 2) * ‖v‖ ^ 2 := by
    calc |F z v v - ‖v‖ ^ 2| = ‖F z v v - ‖v‖ ^ 2‖ := (Real.norm_eq_abs _).symm
      _ = ‖(F z - F 0) v v‖ := by
        rw [sub_apply, sub_apply, h0vv]
      _ ≤ ‖F z - F 0‖ * ‖v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm₂ _ v v
      _ ≤ (1 / 2) * ‖v‖ * ‖v‖ := by gcongr
      _ = (1 / 2) * ‖v‖ ^ 2 := by ring
  have hle := (abs_le.mp hbound).1
  have hge := (abs_le.mp hbound).2
  constructor <;> nlinarith [sq_nonneg ‖v‖]

omit [NeZero (Module.finrank Real E)] in
def FramedCoordMetricDerivBound
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) (p : Nat) (C : Real) : Prop :=
  ∀ z ∈ U, ‖iteratedFDeriv Real p (framedCoordMetric (I := I) Y x) z‖ ≤ C

namespace FramedCoordMetricDerivBound

omit [NeZero (Module.finrank Real E)] in
theorem of_eqOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {U : Set E} (hU : IsOpen U)
    {f : E → E →L[Real] E →L[Real] Real} {p : Nat} {C : Real}
    (heq : Set.EqOn (framedCoordMetric (I := I) Y x) f U)
    (hf : ∀ z ∈ U, ‖iteratedFDeriv Real p f z‖ ≤ C) :
    FramedCoordMetricDerivBound (I := I) Y x U p C := by
  intro z hz
  have hevent : framedCoordMetric (I := I) Y x =ᶠ[nhds z] f :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hz) fun q hq => heq hq
  rw [(Filter.EventuallyEq.iteratedFDeriv Real hevent p).eq_of_nhds]
  exact hf z hz

end FramedCoordMetricDerivBound

omit [NeZero (Module.finrank Real E)] in
theorem framedCoordMetricEquivOn_ball_of_iteratedFDeriv_one_le
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {s C : Real} (hs : 0 < s) (hC : 0 ≤ C)
    (hsm : ContDiffOn Real ∞ (framedCoordMetric (I := I) Y x) (Metric.ball (0 : E) s))
    (hderiv : ∀ z ∈ Metric.ball (0 : E) s,
      ‖iteratedFDeriv Real 1 (framedCoordMetric (I := I) Y x) z‖ ≤ C) :
    FramedCoordMetricEquivOn (I := I) Y x
      (Metric.ball (0 : E) (min s (1 / (2 * C + 1)))) := by
  intro z hz v
  exact metricEquivOn_ball_of_norm_fderiv_le_innerSL hs hC (framedCoordMetric_zero Y x)
    (fun w hw =>
      ((hsm w hw).contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp))
    (fun w hw => by
      rw [← norm_iteratedFDeriv_one (𝕜 := Real) (f := framedCoordMetric (I := I) Y x)]
      exact hderiv w hw)
    z hz v

theorem framedExp_ball_subset_source
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Metric.ball (0 : E) (metricCoerciveExpRadius (I := I) Y.metric x) ⊆
      (framedExpDiffeo (I := I) Y.metric x).source := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  rw [framedExp_source]
  have hzRaw : ‖(normalFrame (I := I) Y.metric x z : E)‖ <
      expMapC2Radius (I := I) Y.metric x := by
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric x
    simpa only [normalFrame_sqrt] using hz
  exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hzRaw

noncomputable def framedNormalBallChart
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
  have hball := framedExp_ball_subset_source (I := I) Y x
  have himage : (fun z : E => framedExpDiffeo (I := I) Y.metric x z) ''
        Metric.ball (0 : E) (metricCoerciveExpRadius (I := I) Y.metric x) =
      framedExpMap (I := I) Y.metric x ''
        Metric.ball (0 : E) (metricCoerciveExpRadius (I := I) Y.metric x) :=
    Set.image_congr fun z hz => framedExp_eq_expMap (I := I) Y.metric x (hball hz)
  exact
    { radius := metricCoerciveExpRadius (I := I) Y.metric x
      radius_pos := metricCoerciveExpRadius_pos (I := I) Y.metric x
      hom := framedExpDiffeo (I := I) Y.metric x
      ball_subset := hball
      map_zero := framedExp_zero (I := I) Y.metric x
      smooth_to := framedExp_smoothOn (I := I) Y x
      smooth_inv := by
        rw [himage]
        exact framedChart_smooth (I := I) Y x }

theorem framed_normal_ball_chart_metric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (framedNormalBallChart (I := I) Y x).metric Y.metric =
      framedCoordMetric (I := I) Y x := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  ext z v w
  rw [NormalBallChart.metric_apply (I := I), framedCoordMetric_apply (I := I)]
  simp only [framedNormalBallChart]
  rfl

theorem framed_normal_ball_chart_metricEquivOn_iff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) (U : Set E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (framedNormalBallChart (I := I) Y x).MetricEquivOn Y.metric U ↔
      FramedCoordMetricEquivOn (I := I) Y x U := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  simp only [NormalBallChart.MetricEquivOn, FramedCoordMetricEquivOn,
    framed_normal_ball_chart_metric (I := I) Y x]

theorem framed_normal_ball_chart_metricDerivBound_iff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) (p : Nat) (C : Real) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (framedNormalBallChart (I := I) Y x).MetricDerivBound Y.metric U p C ↔
      FramedCoordMetricDerivBound (I := I) Y x U p C := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  simp only [NormalBallChart.MetricDerivBound, FramedCoordMetricDerivBound,
    framed_normal_ball_chart_metric (I := I) Y x]

structure FramedCoordMetricBounds
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  A : Real
  A_pos : 0 < A
  metricC : Nat → Real
  metricC_nonneg : ∀ p : Nat, 0 ≤ metricC p
  radius : ∀ k : Nat, (X.obj k).M → Real
  radius_pos : ∀ (k : Nat) (x : (X.obj k).M), 0 < radius k x
  radius_le_A : ∀ (k : Nat) (x : (X.obj k).M), radius k x ≤ A
  metric_equiv : ∀ (k : Nat) (x : (X.obj k).M),
    (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
     letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
     letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
     riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
       ENNReal.ofReal A) →
      FramedCoordMetricEquivOn (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x))
  metric_deriv : ∀ (k p : Nat) (x : (X.obj k).M),
    (letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
     letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
     letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
     riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
       ENNReal.ofReal A) →
      FramedCoordMetricDerivBound (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x)) p (metricC p)

namespace FramedCoordMetricBounds

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : FramedCoordMetricBounds (I := I) X) (f : Nat → Nat) :
    FramedCoordMetricBounds (I := I) (X.subseq f) where
  A := h.A
  A_pos := h.A_pos
  metricC := h.metricC
  metricC_nonneg := h.metricC_nonneg
  radius k x := h.radius (f k) x
  radius_pos k x := h.radius_pos (f k) x
  radius_le_A k x := h.radius_le_A (f k) x
  metric_equiv := by
    intro k x hx
    with_unfolding_all exact h.metric_equiv (f k) x hx
  metric_deriv := by
    intro k p x hx
    with_unfolding_all exact h.metric_deriv (f k) p x hx

def metricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : FramedCoordMetricBounds (I := I) X) (k : Nat) (x : (X.obj k).M)
    (hx : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
        ENNReal.ofReal h.A) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    (framedNormalBallChart (I := I) (X.obj k) x).MetricBounds (X.obj k).metric := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  exact
    { C := h.metricC
      C_nonneg := h.metricC_nonneg
      radius := h.radius k x
      radius_pos := h.radius_pos k x
      equiv := (framed_normal_ball_chart_metricEquivOn_iff (I := I) (X.obj k) x
        (Metric.ball (0 : E) (h.radius k x))).mpr (h.metric_equiv k x hx)
      deriv := fun p =>
        (framed_normal_ball_chart_metricDerivBound_iff (I := I) (X.obj k) x
          (Metric.ball (0 : E) (h.radius k x)) p (h.metricC p)).mpr
          (h.metric_deriv k p x hx) }

end FramedCoordMetricBounds

noncomputable def framedNormalChartFamily
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    NormalChartFamily (I := I) X :=
  fun k x => framedNormalBallChart (I := I) (X.obj k) x

theorem framed_normal_chart_family_metric
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    (framedNormalChartFamily (I := I) X).metric k x =
      framedCoordMetric (I := I) (X.obj k) x := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  simpa only [NormalChartFamily.metric, framedNormalChartFamily] using
    framed_normal_ball_chart_metric (I := I) (X.obj k) x

end CheegerGromovCompactness
end DifferentialGeometry
