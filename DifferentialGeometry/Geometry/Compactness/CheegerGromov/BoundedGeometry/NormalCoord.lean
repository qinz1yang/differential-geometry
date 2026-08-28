import DifferentialGeometry.Geometry.Comparison.Volume.RadialRadius


import DifferentialGeometry.Geometry.Comparison.Volume.BallVolume
import DifferentialGeometry.Analysis.Calculus.MapConvergenceDeriv
import DifferentialGeometry.Geometry.Exponential.FramedNormalCoordinates
import DifferentialGeometry.Geometry.Exponential.IntrinsicBallChart
import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicGronwall
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.BoundedGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.EMetric
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.Inputs
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Set
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intr_metric_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M :=
      IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    letI : ConnectedSpace Y.M := hconn
    let hEnorm : ∀ (y : Y.M) (w : TangentSpace I y),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y w w)) := by
      intro y w
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric y w
    ∀ {z : E}, z ∈
        (intrFrameDiffeo (I := I) Y.metric hEnorm x).source →
      intrFrameMetric (I := I) Y.metric hEnorm x z =
        NormalCoordinates.framedMetric (I := I) Y.metric x z := by
  let _ := hconn
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let : ConnectedSpace Y.M := by
    exact hconn
  let hEnorm : ∀ (y : Y.M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y w w)) := by
    intro y w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) Y.metric y w
  change ∀ {z : E}, z ∈
      (intrFrameDiffeo (I := I) Y.metric hEnorm x).source →
    intrFrameMetric (I := I) Y.metric hEnorm x z =
      NormalCoordinates.framedMetric (I := I) Y.metric x z
  intro z hz
  exact intrFrameMetric_eq (I := I) Y.metric hEnorm x (z := z) hz

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_intr_eq_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M :=
      IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    letI : ConnectedSpace Y.M := hconn
    let hEnorm : ∀ (y : Y.M) (w : TangentSpace I y),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y w w)) := by
      intro y w
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric y w
    ∃ r : Real, 0 < r ∧ ∀ z ∈ Metric.ball (0 : E) r,
      intrFrameMetric (I := I) Y.metric hEnorm x z =
        NormalCoordinates.framedMetric (I := I) Y.metric x z := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let : ConnectedSpace Y.M := hconn
  let hEnorm : ∀ (y : Y.M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y w w)) := by
    intro y w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) Y.metric y w
  change ∃ r : Real, 0 < r ∧ ∀ z ∈ Metric.ball (0 : E) r,
    intrFrameMetric (I := I) Y.metric hEnorm x z =
      NormalCoordinates.framedMetric (I := I) Y.metric x z
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (intrFrameDiffeo (I := I) Y.metric hEnorm x).open_source
      0 (zero_mem_intrFrame_source (I := I) Y.metric hEnorm x)
  refine ⟨r, hr, fun z hz => ?_⟩
  exact intr_metric_eq (I := I) Y hcomplete hconn x (hball hz)

def FramedNormalCoordMetricEquivOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) (U : Set E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Prop := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact ∀ z ∈ U, ∀ v : E,
    (1 / 2 : Real) * ‖v‖ ^ 2 ≤
        NormalCoordinates.framedMetric (I := I) Y.metric x z v v ∧
      NormalCoordinates.framedMetric (I := I) Y.metric x z v v ≤
        2 * ‖v‖ ^ 2

def framedJacobiRadius
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Real := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact expRadiusGp (I := I) Y.metric x / 26

lemma framedJacobiRadius_pos
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    0 < framedJacobiRadius (I := I) Y x := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [framedJacobiRadius]
  exact div_pos (expRadiusGp_pos (I := I) Y.metric x) (by norm_num)

lemma normalFrame_lt_jac
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {z : E} :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ‖z‖ < framedJacobiRadius (I := I) Y x →
      ‖normalFrame (I := I) Y.metric x z‖ <
        jacobiVarRadius (I := I) Y.metric x := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hz
  rw [framedJacobiRadius] at hz
  rw [jacobiVarRadius]
  apply norm_lt_exp_div (I := I) Y.metric x (by norm_num)
  simpa only [normalFrame_sqrt] using hz

def FramedRm04Bound
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E) (R : Real) : Prop :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  ∀ t ∈ Set.Ioo (0 : Real) 1,
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) Y.metric
      (radialCurve (I := I) Y.metric x
        (normalFrame (I := I) Y.metric x z) t) 4
      (DifferentialGeometry.Geometry.Curvature.metricRm04At
        (I := I) (M := Y.M) Y.metric
        (radialCurve (I := I) Y.metric x
          (normalFrame (I := I) Y.metric x z) t))) ≤ R

omit [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem framed_rm04_of_seq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqBoundedGeometry (I := I) X) (k : Nat)
    (x : (X.obj k).M) (z : E) :
    FramedRm04Bound (I := I) (X.obj k) x z (hX.C 0) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  intro t ht
  exact rm04Bound_of_seq (I := I) hX k
    (radialCurve (I := I) (X.obj k).metric x
      (normalFrame (I := I) (X.obj k).metric x z) t)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intr_rm04_of_seq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hX : SeqBoundedGeometry (I := I) X) (k : Nat)
    (x : (X.obj k).M) (z : E) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M :=
      IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    letI : ConnectedSpace (X.obj k).M := hconn k
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj k).metric y w
    IntrinsicRm04Bound (I := I) (X.obj k).metric hEnorm x
      (normalFrame (I := I) (X.obj k).metric x z) (hX.C 0) := by
  let _ := hconn
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M :=
    IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  let : ConnectedSpace (X.obj k).M := hconn k
  let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) (X.obj k).metric y w
  change ∀ t ∈ Set.Ico (0 : Real) 1,
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) (X.obj k).metric
      (intrinsicGeodesic (I := I) (X.obj k).metric hEnorm x
        (normalFrame (I := I) (X.obj k).metric x z) t) 4
      (DifferentialGeometry.Geometry.Curvature.metricRm04At
        (I := I) (M := (X.obj k).M) (X.obj k).metric
        (intrinsicGeodesic (I := I) (X.obj k).metric hEnorm x
          (normalFrame (I := I) (X.obj k).metric x z) t))) ≤ hX.C 0
  intro t _ht
  exact rm04Bound_of_seq (I := I) hX k
    (intrinsicGeodesic (I := I) (X.obj k).metric hEnorm x
      (normalFrame (I := I) (X.obj k).metric x z) t)

theorem framed_metric_jacobi
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    let L : E ≃L[Real] E :=
      (normalFrame (I := I) Y.metric x).trans
        (tangentSpaceModelContinuousLinearEquiv (I := I) x)
    ‖z‖ < expRadiusGp (I := I) Y.metric x →
    NormalCoordinates.framedMetric (I := I) Y.metric x z v w =
      Y.metric.inner
        (expMap (I := I) Y.metric x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L z)))
        (radialJacobiField (I := I) Y.metric x
          (L z) (L v) 1)
        (radialJacobiField (I := I) Y.metric x
          (L z) (L w) 1) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  dsimp only
  let L : E ≃L[Real] E :=
    (normalFrame (I := I) Y.metric x).trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) x)
  change ‖z‖ < expRadiusGp (I := I) Y.metric x →
    NormalCoordinates.framedMetric (I := I) Y.metric x z v w =
      Y.metric.inner
        (expMap (I := I) Y.metric x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L z)))
        (radialJacobiField (I := I) Y.metric x (L z) (L v) 1)
        (radialJacobiField (I := I) Y.metric x (L z) (L w) 1)
  intro hz
  have hzC2 : ‖L z‖ <
      expMapC2Radius (I := I) Y.metric x := by
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric x
    change Real.sqrt (Y.metric.inner x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L z))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L z))) < _
    have hLz : (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L z) =
        normalFrame (I := I) Y.metric x z := by
      dsimp only [L]
      rw [ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    rw [hLz]
    simpa only [normalFrame_sqrt] using hz
  have hsrc : z ∈ (framedExpDiffeo (I := I) Y.metric x).source := by
    rw [framedExp_source]
    change L z ∈ (expMapDiffeo (I := I) Y.metric x).source
    exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hzC2
  have hraw : L z ∈ (expMapDiffeo (I := I) Y.metric x).source := by
    rw [framedExp_source] at hsrc
    change L z ∈ (expMapDiffeo (I := I) Y.metric x).source at hsrc
    exact hsrc
  rw [NormalCoordinates.framedMetric_apply (I := I), framedExp_apply,
    mfderiv_framedExp (I := I) Y.metric x hsrc]
  change Y.metric.inner
      (expMapDiffeo (I := I) Y.metric x (L z))
      (((mfderiv 𝓘(Real, E) I
        (fun u : E => expMapDiffeo (I := I) Y.metric x u) (L z)).comp
          L.toContinuousLinearMap) v)
      (((mfderiv 𝓘(Real, E) I
        (fun u : E => expMapDiffeo (I := I) Y.metric x u) (L z)).comp
          L.toContinuousLinearMap) w) = _
  rw [expMapDiffeo_apply_eq (I := I) Y.metric x hraw,
    expDiffeo_mfderiv (I := I) Y.metric x hraw]
  have hvJac := radialJacobi_one (I := I) Y.metric x (L z) (L v) hzC2
  have hwJac := radialJacobi_one (I := I) Y.metric x (L z) (L w) hzC2
  simp only [tangentSpaceModelContinuousLinearEquiv_symm_apply] at hvJac hwJac
  rw [hvJac, hwJac]
  rfl

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem framed_rm04_bounds
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (x : Y.M) (z v : E) {a K R Vb A Blo Bhi : Real}
    (ha : 0 < a) (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (hz : ‖z‖ < framedJacobiRadius (I := I) Y x)
    (hav : ‖a • v‖ < framedJacobiRadius (I := I) Y x)
    (hlaunch : ‖z‖ ≤ Vb) (hinit : ‖a • v‖ ≤ A)
    (hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
          R * Vb ^ 2 ≤ K)
    (hRm : FramedRm04Bound (I := I) Y x z R)
    (hmodelLe :
      A + gronwallBound 0 (max K 1) (K * A) 1 ≤ a * Bhi)
    (hmodelGe :
      a * Blo ≤ ‖a • v‖ -
        gronwallBound 0 (max K 1) (K * ‖a • v‖) 1) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Blo ≤ Real.sqrt
        (NormalCoordinates.framedMetric (I := I) Y.metric x z v v) ∧
      Real.sqrt
        (NormalCoordinates.framedMetric (I := I) Y.metric x z v v) ≤ Bhi := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let xRaw : E := show E from normalFrame (I := I) Y.metric x z
  let vRaw : E := show E from normalFrame (I := I) Y.metric x v
  have hzDef : ‖z‖ < expRadiusGp (I := I) Y.metric x / 26 := by
    have hz' := hz
    rw [framedJacobiRadius] at hz'
    exact hz'
  have hsmul : a • vRaw =
      (show E from normalFrame (I := I) Y.metric x (a • v)) := by
    dsimp only [vRaw]
    exact ((normalFrame (I := I) Y.metric x).map_smul a v).symm
  have hzRaw : ‖xRaw‖ < jacobiVarRadius (I := I) Y.metric x := by
    dsimp only [xRaw]
    rw [jacobiVarRadius]
    apply norm_lt_exp_div (I := I) Y.metric x (by norm_num)
    simpa only [normalFrame_sqrt] using hzDef
  have havRaw : ‖a • vRaw‖ <
      jacobiVarRadius (I := I) Y.metric x := by
    rw [jacobiVarRadius]
    apply norm_lt_exp_div (I := I) Y.metric x (by norm_num)
    rw [hsmul, normalFrame_sqrt]
    exact hav
  have hzMem : xRaw ∈
      Metric.ball (0 : E) (jacobiVarRadius (I := I) Y.metric x) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hzRaw
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hEnorm : ∀ (y : Y.M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y w w)) := by
    intro y w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) Y.metric y w
  obtain ⟨D, hcard, hpar, hON, hFdiff⟩ :=
    exists_rm04FrameData_radius.{_, _, _, 0} (I := I) Y.metric x
      (R := jacobiVarRadius (I := I) Y.metric x) (b := 1)
      (by norm_num) le_rfl (jacobi_radius_le_c2 (I := I) Y.metric x)
  have hzC2 :
      ‖xRaw‖ < expMapC2Radius (I := I) Y.metric x :=
    hzRaw.trans_le (jacobi_radius_le_c2 (I := I) Y.metric x)
  have hgamma : ∀ t ∈ Set.Icc (0 : Real) 1,
      ContMDiffAt 𝓘(Real, Real) I 1
        (radialCurve (I := I) Y.metric x xRaw) t := by
    intro t ht
    exact (radialCurve_contMDiffAt_Icc (I := I) Y.metric x
      xRaw le_rfl hzC2 t ht).of_le (by norm_num)
  have hlaunchRaw :
      Real.sqrt (Y.metric.inner x xRaw xRaw) ≤ Vb := by
    dsimp only [xRaw]
    simpa only [normalFrame_sqrt] using hlaunch
  have hscaled :
      Real.sqrt (Y.metric.inner x (a • vRaw) (a • vRaw)) = ‖a • v‖ := by
    rw [hsmul, normalFrame_sqrt]
  have hinitRaw :
      Real.sqrt (Y.metric.inner x (a • vRaw) (a • vRaw)) ≤ A := by
    rw [hscaled]
    exact hinit
  have hRmRaw : ∀ t ∈ Set.Ioo (0 : Real) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) Y.metric
        (radialCurve (I := I) Y.metric x xRaw t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := Y.M) Y.metric
          (radialCurve (I := I) Y.metric x xRaw t))) ≤ R := by
    simpa only [FramedRm04Bound, xRaw] using hRm
  have hupper := rm04_one_le (I := I) Y.metric hEnorm x
    xRaw vRaw
    ha hK hVb (by norm_num) le_rfl le_rfl hzRaw havRaw hlaunchRaw
    hKbound hRmRaw hgamma (hcard _ hzMem) (D.F _)
    (hpar _ hzMem) (hON _ hzMem) (hFdiff _ hzMem) hinitRaw
    (by simpa only [one_mul] using hmodelLe)
  have hlower := rm04_one_ge (I := I) Y.metric hEnorm x
    xRaw vRaw
    ha hK hVb (by norm_num) le_rfl le_rfl hzRaw havRaw hlaunchRaw
    hKbound hRmRaw hgamma (hcard _ hzMem) (D.F _)
    (hpar _ hzMem) (hON _ hzMem) (hFdiff _ hzMem)
    (by simpa only [one_mul, hscaled] using hmodelGe)
  have hzGp : ‖z‖ < expRadiusGp (I := I) Y.metric x := by
    rw [framedJacobiRadius] at hz
    have hpos := expRadiusGp_pos (I := I) Y.metric x
    linarith
  rw [framed_metric_jacobi (I := I) Y x z v v hzGp]
  exact ⟨hlower, hupper⟩

private lemma exists_pos_mul_sq_le {S κ : Real} (hκ : 0 < κ) :
    ∃ r : Real, 0 < r ∧ S * r ^ 2 ≤ κ := by
  let T : Real := max S 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right S 1)
  have hdiv : 0 < κ / T := div_pos hκ hT
  refine ⟨Real.sqrt (κ / T), Real.sqrt_pos.mpr hdiv, ?_⟩
  calc
    S * Real.sqrt (κ / T) ^ 2 ≤
        T * Real.sqrt (κ / T) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left S 1) (sq_nonneg _)
    _ = T * (κ / T) := by rw [Real.sq_sqrt hdiv.le]
    _ = κ := by field_simp [hT.ne']

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_smul_lt (v : E) {r : Real} (hr : 0 < r) :
    ∃ a : Real, 0 < a ∧ ‖a • v‖ < r := by
  let d : Real := ‖v‖ + 1
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  let a : Real := r / d
  have ha : 0 < a := div_pos hr hd
  refine ⟨a, ha, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have hv : ‖v‖ < d := by
    dsimp only [d]
    linarith
  calc
    a * ‖v‖ < a * d := mul_lt_mul_of_pos_left hv ha
    _ = r := by
      dsimp only [a]
      field_simp [hd.ne']

private lemma quarter_models {K s : Real} (hs : 0 ≤ s)
    (herr : gronwallBound 0 (max K 1) K 1 ≤ 1 / 4) :
    s + gronwallBound 0 (max K 1) (K * s) 1 ≤ (5 / 4) * s ∧
      (3 / 4) * s ≤ s - gronwallBound 0 (max K 1) (K * s) 1 := by
  have hscale :
      gronwallBound 0 (max K 1) (K * s) 1 =
        s * gronwallBound 0 (max K 1) K 1 := by
    have heps : K * s = s * K := by ring
    rw [heps, gronwallBound_zero_mul_eps]
  have hmul := mul_le_mul_of_nonneg_left herr hs
  rw [hscale]
  constructor <;> nlinarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_intr_radii
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X) :
    ∃ r₀ : Real, 0 < r₀ ∧ ∀ (k : Nat) (x : (X.obj k).M),
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : IsManifold I 1 (X.obj k).M :=
        IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
        Manifold.metrizableSpace I (X.obj k).M
      letI : T3Space (X.obj k).M := inferInstance
      letI : RiemannianBundle
          (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle (I := I)
      letI : (y : (X.obj k).M) →
          InnerProductSpace Real (TangentSpace I y) :=
        (X.obj k).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj k).M :=
        (X.obj k).emetricSpace (I := I)
      letI : CompleteSpace (X.obj k).M :=
        MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
      letI : ConnectedSpace (X.obj k).M := hconn k
      let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
          ‖w‖ₑ =
            ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
        intro y w
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w
      ∀ z ∈ Metric.ball (0 : E) r₀, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤
            intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ∧
          intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ≤
            2 * ‖v‖ ^ 2 := by
  obtain ⟨κ, buffer, hκ, hbuffer, hsmall⟩ :=
    exists_gron_smallK (B₀ := (1 / 4 : Real)) (D := 1)
      (by norm_num) (by norm_num)
  let S : Real :=
    Real.sqrt ((Fintype.card
      (Fin (Module.finrank Real E)) : Real)) * hgeom.C 0
  have hS : 0 ≤ S :=
    mul_nonneg (Real.sqrt_nonneg _) (hgeom.nonneg 0)
  obtain ⟨r₀, hr₀, hcap⟩ := exists_pos_mul_sq_le (S := S) hκ
  refine ⟨r₀, hr₀, ?_⟩
  intro k x
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M :=
    IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  let : ConnectedSpace (X.obj k).M := hconn k
  let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) (X.obj k).metric y w
  change ∀ z ∈ Metric.ball (0 : E) r₀, ∀ v : E,
    (1 / 2 : Real) * ‖v‖ ^ 2 ≤
        intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ∧
      intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ≤
        2 * ‖v‖ ^ 2
  intro z hz v
  have hzRadius : ‖z‖ < r₀ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  let u : TangentSpace I x :=
    normalFrame (I := I) (X.obj k).metric x z
  let w : TangentSpace I x :=
    normalFrame (I := I) (X.obj k).metric x v
  let K : Real :=
    Real.sqrt ((Fintype.card
      (Fin (Module.finrank Real E)) : Real)) *
        hgeom.C 0 * (X.obj k).metric.inner x u u
  have hK : 0 ≤ K := by
    dsimp only [K, u]
    rw [normalFrame_normSq]
    change 0 ≤ S * ‖z‖ ^ 2
    exact mul_nonneg hS (sq_nonneg ‖z‖)
  have hsq : ‖z‖ ^ 2 ≤ r₀ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg z) hr₀.le).2 hzRadius.le
  have hKle : K ≤ κ := by
    calc
      K = S * ‖z‖ ^ 2 := by
        simp only [K, S, u, normalFrame_normSq]
      _ ≤ S * r₀ ^ 2 := mul_le_mul_of_nonneg_left hsq hS
      _ ≤ κ := hcap
  have herr : gronwallBound 0 (max K 1) K 1 ≤ 1 / 4 := by
    have hsmallK := hsmall hK hKle
    have hsmallK' :
        buffer ≤ (1 / 4 : Real) -
          gronwallBound 0 (max K 1) K 1 := by
      simpa only [mul_one] using hsmallK
    linarith
  obtain ⟨hmodelLe, hmodelGe⟩ :=
    quarter_models (K := K) (s := ‖v‖) (norm_nonneg _) herr
  have hRm :=
    intr_rm04_of_seq (I := I) hcomplete hconn hgeom k x z
  have hODE :=
    intrJacobi_ode (I := I) (X.obj k).metric hEnorm x u w
      (hgeom.nonneg 0) hRm
  obtain ⟨hupper, hlower⟩ :=
    intrJacobi_bounds (I := I) (X.obj k).metric hEnorm x u w
      hK zero_lt_one (by simpa only [K] using hODE)
  have hupper1 := hupper 1 (by norm_num)
  have hlower1 := hlower 1 (by norm_num)
  have hwNorm :
      Real.sqrt ((X.obj k).metric.inner x w w) = ‖v‖ := by
    simpa only [w] using
      normalFrame_sqrt (I := I) (X.obj k).metric x v
  simp only [one_mul, hwNorm] at hupper1 hlower1
  let q : (X.obj k).M :=
    intrinsicGeodesic (I := I) (X.obj k).metric hEnorm x u 1
  let J : TangentSpace I q :=
    intrinsicJacobi (I := I) (X.obj k).metric hEnorm x u w 1
  have hsqrtUpper :
      Real.sqrt ((X.obj k).metric.inner q J J) ≤
        (5 / 4 : Real) * ‖v‖ :=
    hupper1.trans hmodelLe
  have hsqrtLower :
      (3 / 4 : Real) * ‖v‖ ≤
        Real.sqrt ((X.obj k).metric.inner q J J) :=
    hmodelGe.trans hlower1
  have hmetricNonneg : 0 ≤ (X.obj k).metric.inner q J J := by
    rcases eq_or_ne J 0 with hJ | hJ
    · simp [hJ]
    · exact ((X.obj k).metric.pos q J hJ).le
  have hlowerSq :
      ((3 / 4 : Real) * ‖v‖) ^ 2 ≤
        (Real.sqrt ((X.obj k).metric.inner q J J)) ^ 2 :=
    (sq_le_sq₀
      (mul_nonneg (by norm_num) (norm_nonneg v))
      (Real.sqrt_nonneg _)).2 hsqrtLower
  have hupperSq :
      (Real.sqrt ((X.obj k).metric.inner q J J)) ^ 2 ≤
        ((5 / 4 : Real) * ‖v‖) ^ 2 :=
    (sq_le_sq₀
      (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (norm_nonneg v))).2 hsqrtUpper
  rw [Real.sq_sqrt hmetricNonneg] at hlowerSq hupperSq
  have hmetric :
      intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v =
        (X.obj k).metric.inner q J J := by
    rw [intr_metric_jacobi (I := I) (X.obj k).metric hEnorm x z v v]
    dsimp only [q, J, u, w, intrinsicFramedExp, expMapIntrinsic]
    rw [intrFrameCLM_apply]
    rfl
  rw [hmetric]
  constructor <;> nlinarith [sq_nonneg ‖v‖]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_intr_branches
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X) :
    ∃ r₀ : Real, 0 < r₀ ∧ ∀ (k : Nat) (x : (X.obj k).M),
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : IsManifold I 1 (X.obj k).M :=
        IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
        Manifold.metrizableSpace I (X.obj k).M
      letI : T3Space (X.obj k).M := inferInstance
      letI : RiemannianBundle
          (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle (I := I)
      letI : (y : (X.obj k).M) →
          InnerProductSpace Real (TangentSpace I y) :=
        (X.obj k).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj k).M :=
        (X.obj k).emetricSpace (I := I)
      letI : CompleteSpace (X.obj k).M :=
        MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
      letI : ConnectedSpace (X.obj k).M := hconn k
      let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
          ‖w‖ₑ =
            ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
        intro y w
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w
      ∀ z ∈ Metric.ball (0 : E) r₀,
        ∃ B : ExpInvBranch (I := I) (X.obj k).metric hEnorm x,
          (normalFrame (I := I) (X.obj k).metric x z : E) ∈
            B.hom.source := by
  obtain ⟨r₀, hr₀, hmetric⟩ :=
    exists_intr_radii (I := I) X hcomplete hconn hgeom
  refine ⟨r₀, hr₀, ?_⟩
  intro k x
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M :=
    IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  let : ConnectedSpace (X.obj k).M := hconn k
  let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) (X.obj k).metric y w
  change ∀ z ∈ Metric.ball (0 : E) r₀,
    ∃ B : ExpInvBranch (I := I) (X.obj k).metric hEnorm x,
      (normalFrame (I := I) (X.obj k).metric x z : E) ∈ B.hom.source
  intro z hz
  have hlower : ∀ v : E, (1 / 2 : Real) * ‖v‖ ^ 2 ≤
      intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v :=
    fun v => (hmetric k x z hz v).1
  have hnot :
      ¬ IsConjVec (I := I) (X.obj k).metric hEnorm x
        (normalFrame (I := I) (X.obj k).metric x z : E) :=
    intrFrame_not_conj (I := I) (X.obj k).metric hEnorm x z
      (by norm_num) hlower
  exact branch_of_not_conj (I := I) (X.obj k).metric hEnorm hnot

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_intr_localOn
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X) :
    ∃ r₀ : Real, 0 < r₀ ∧ ∀ (k : Nat) (x : (X.obj k).M),
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : IsManifold I 1 (X.obj k).M :=
        IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
        Manifold.metrizableSpace I (X.obj k).M
      letI : T3Space (X.obj k).M := inferInstance
      letI : RiemannianBundle
          (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle (I := I)
      letI : (y : (X.obj k).M) →
          InnerProductSpace Real (TangentSpace I y) :=
        (X.obj k).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj k).M :=
        (X.obj k).emetricSpace (I := I)
      letI : CompleteSpace (X.obj k).M :=
        MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
      letI : ConnectedSpace (X.obj k).M := hconn k
      let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
          ‖w‖ₑ =
            ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
        intro y w
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞
        (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
        (Metric.ball (0 : E) r₀) := by
  obtain ⟨r₀, hr₀, hbranch⟩ :=
    exists_intr_branches (I := I) X hcomplete hconn hgeom
  refine ⟨r₀, hr₀, ?_⟩
  intro k x
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M :=
    IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  let : ConnectedSpace (X.obj k).M := hconn k
  let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) (X.obj k).metric y w
  exact intrFrame_localOn (I := I) (X.obj k).metric hEnorm x
    (Metric.ball (0 : E) r₀) (hbranch k x)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_intr_control
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X) :
    ∃ r₀ : Real, 0 < r₀ ∧ ∀ (k : Nat) (x : (X.obj k).M),
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : IsManifold I 1 (X.obj k).M :=
        IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
        Manifold.metrizableSpace I (X.obj k).M
      letI : T3Space (X.obj k).M := inferInstance
      letI : RiemannianBundle
          (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle (I := I)
      letI : (y : (X.obj k).M) →
          InnerProductSpace Real (TangentSpace I y) :=
        (X.obj k).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : (X.obj k).M => TangentSpace I y) :=
        (X.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj k).M :=
        (X.obj k).emetricSpace (I := I)
      letI : CompleteSpace (X.obj k).M :=
        MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
      letI : ConnectedSpace (X.obj k).M := hconn k
      let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
          ‖w‖ₑ =
            ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
        intro y w
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w
      (∀ z ∈ Metric.ball (0 : E) r₀, ∀ v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤
              intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ∧
            intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ≤
              2 * ‖v‖ ^ 2) ∧
        IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞
          (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
          (Metric.ball (0 : E) r₀) := by
  obtain ⟨rMetric, hrMetric, hmetric⟩ :=
    exists_intr_radii (I := I) X hcomplete hconn hgeom
  obtain ⟨rLocal, hrLocal, hlocal⟩ :=
    exists_intr_localOn (I := I) X hcomplete hconn hgeom
  refine ⟨min rMetric rLocal, lt_min hrMetric hrLocal, ?_⟩
  intro k x
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M :=
    IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  let : ConnectedSpace (X.obj k).M := hconn k
  let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) (X.obj k).metric y w
  have hmetricSub :
      Metric.ball (0 : E) (min rMetric rLocal) ⊆
        Metric.ball (0 : E) rMetric :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hlocalSub :
      Metric.ball (0 : E) (min rMetric rLocal) ⊆
        Metric.ball (0 : E) rLocal :=
    Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨?_, ?_⟩
  · intro z hz v
    exact hmetric k x z (hmetricSub hz) v
  · intro z
    exact hlocal k x ⟨z.1, hlocalSub z.2⟩

theorem exists_rm04_radii
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hgeom : SeqBoundedGeometry (I := I) X) :
    ∃ r₀ : Real, 0 < r₀ ∧ ∀ (k : Nat) (x : (X.obj k).M),
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      FramedNormalCoordMetricEquivOn (I := I) (X.obj k) x
        (Metric.ball (0 : E)
          (min (framedJacobiRadius (I := I) (X.obj k) x) r₀)) := by
  obtain ⟨κ, buffer, hκ, hbuffer, hsmall⟩ :=
    exists_gron_smallK (B₀ := (1 / 4 : Real)) (D := 1)
      (by norm_num) (by norm_num)
  let S : Real :=
    Real.sqrt ((Fintype.card
      (Fin 1 -> Fin (Module.finrank Real E)) : Real)) * hgeom.C 0
  have hS : 0 ≤ S := by
    exact mul_nonneg (Real.sqrt_nonneg _) (hgeom.nonneg 0)
  obtain ⟨r₀, hr₀, hcap⟩ := exists_pos_mul_sq_le (S := S) hκ
  refine ⟨r₀, hr₀, ?_⟩
  intro k x
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let K : Real := S * r₀ ^ 2
  have hK : 0 ≤ K := mul_nonneg hS (sq_nonneg r₀)
  have hKle : K ≤ κ := by simpa only [K] using hcap
  have herr : gronwallBound 0 (max K 1) K 1 ≤ 1 / 4 := by
    have hsmallK := hsmall hK hKle
    have hsmallK' :
        buffer ≤ (1 / 4 : Real) - gronwallBound 0 (max K 1) K 1 := by
      simpa only [mul_one] using hsmallK
    linarith
  intro z hz v
  have hzMin :
      ‖z‖ < min (framedJacobiRadius (I := I) (X.obj k) x) r₀ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzJac : ‖z‖ < framedJacobiRadius (I := I) (X.obj k) x :=
    hzMin.trans_le (min_le_left _ _)
  have hzRadius : ‖z‖ < r₀ := hzMin.trans_le (min_le_right _ _)
  obtain ⟨a, ha, hav⟩ := exists_smul_lt (v := v)
    (framedJacobiRadius_pos (I := I) (X.obj k) x)
  have hnormScale : ‖a • v‖ = a * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  obtain ⟨hmodelLe₀, hmodelGe₀⟩ :=
    quarter_models (K := K) (s := ‖a • v‖) (norm_nonneg _) herr
  have hmodelLe :
      ‖a • v‖ + gronwallBound 0 (max K 1) (K * ‖a • v‖) 1 ≤
        a * ((5 / 4 : Real) * ‖v‖) := by
    calc
      ‖a • v‖ + gronwallBound 0 (max K 1) (K * ‖a • v‖) 1 ≤
          (5 / 4 : Real) * ‖a • v‖ := hmodelLe₀
      _ = a * ((5 / 4 : Real) * ‖v‖) := by rw [hnormScale]; ring
  have hmodelGe :
      a * ((3 / 4 : Real) * ‖v‖) ≤
        ‖a • v‖ - gronwallBound 0 (max K 1) (K * ‖a • v‖) 1 := by
    calc
      a * ((3 / 4 : Real) * ‖v‖) =
          (3 / 4 : Real) * ‖a • v‖ := by rw [hnormScale]; ring
      _ ≤ ‖a • v‖ - gronwallBound 0 (max K 1) (K * ‖a • v‖) 1 :=
        hmodelGe₀
  have hKbound :
      Real.sqrt ((Fintype.card
        (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
          hgeom.C 0 * r₀ ^ 2 ≤ K := by
    simp only [K, S]
    exact le_rfl
  have hbounds := framed_rm04_bounds (I := I) (X.obj k)
    (hcomplete.complete k) x z v
    (a := a) (K := K) (R := hgeom.C 0) (Vb := r₀)
    (A := ‖a • v‖) (Blo := (3 / 4 : Real) * ‖v‖)
    (Bhi := (5 / 4 : Real) * ‖v‖)
    ha hK hr₀.le hzJac hav hzRadius.le le_rfl hKbound
    (framed_rm04_of_seq (I := I) hgeom k x z) hmodelLe hmodelGe
  have hzGp : ‖z‖ < expRadiusGp (I := I) (X.obj k).metric x := by
    rw [framedJacobiRadius] at hzJac
    have hpos := expRadiusGp_pos (I := I) (X.obj k).metric x
    linarith
  have hmetricNonneg :
      0 ≤ NormalCoordinates.framedMetric
        (I := I) (X.obj k).metric x z v v := by
    rw [framed_metric_jacobi (I := I) (X.obj k) x z v v hzGp]
    let q : (X.obj k).M :=
      expMap (I := I) (X.obj k).metric x
        (normalFrame (I := I) (X.obj k).metric x z)
    let J : TangentSpace I q :=
      radialJacobiField (I := I) (X.obj k).metric x
        (normalFrame (I := I) (X.obj k).metric x z)
        (normalFrame (I := I) (X.obj k).metric x v) 1
    change 0 ≤ (X.obj k).metric.inner q J J
    rcases eq_or_ne J 0 with hJ | hJ
    · rw [hJ]
      simp
    · exact ((X.obj k).metric.pos q J hJ).le
  have hlowerSq :
      ((3 / 4 : Real) * ‖v‖) ^ 2 ≤
        (Real.sqrt (NormalCoordinates.framedMetric
          (I := I) (X.obj k).metric x z v v)) ^ 2 :=
    (sq_le_sq₀
      (mul_nonneg (by norm_num) (norm_nonneg v))
      (Real.sqrt_nonneg _)).2 hbounds.1
  have hupperSq :
      (Real.sqrt (NormalCoordinates.framedMetric
        (I := I) (X.obj k).metric x z v v)) ^ 2 ≤
        ((5 / 4 : Real) * ‖v‖) ^ 2 :=
    (sq_le_sq₀
      (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (norm_nonneg v))).2 hbounds.2
  rw [Real.sq_sqrt hmetricNonneg] at hlowerSq hupperSq
  constructor <;> nlinarith [sq_nonneg ‖v‖]

theorem framed_equiv_jacobi
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (∀ z ∈ U, ‖z‖ < expRadiusGp (I := I) Y.metric x) →
    (∀ z ∈ U, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
        Y.metric.inner
          (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z))
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1)
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1) ∧
        Y.metric.inner
          (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z))
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1)
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1) ≤
              2 * ‖v‖ ^ 2) →
    FramedNormalCoordMetricEquivOn (I := I) Y x U := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hsmall hJ z hz v
  rw [framed_metric_jacobi (I := I) Y x z v v (hsmall z hz)]
  exact hJ z hz v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma half_two_of_close
    (G G₀ : E →L[Real] E →L[Real] Real)
    (hG : ‖G - G₀‖ ≤ 1 / 2)
    (hG₀ : ∀ v : E, G₀ v v = ‖v‖ ^ 2)
    (v : E) :
    (1 / 2 : Real) * ‖v‖ ^ 2 ≤ G v v ∧ G v v ≤ 2 * ‖v‖ ^ 2 := by
  have hdiff :
      (G - G₀) v v = G v v - ‖v‖ ^ 2 := by
    simp only [sub_apply, hG₀]
  have heval := ContinuousLinearMap.le_opNorm₂
    (G - G₀) v v
  have habs : |G v v - ‖v‖ ^ 2| ≤ (1 / 2 : Real) * ‖v‖ ^ 2 := by
    calc
      |G v v - ‖v‖ ^ 2| =
          ‖(G - G₀) v v‖ := by
            rw [hdiff, Real.norm_eq_abs]
      _ ≤ ‖G - G₀‖ * ‖v‖ * ‖v‖ := heval
      _ = ‖G - G₀‖ * ‖v‖ ^ 2 := by ring
      _ ≤ (1 / 2 : Real) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hG (sq_nonneg ‖v‖)
  obtain ⟨hlower, hupper⟩ := abs_le.mp habs
  constructor <;> nlinarith [sq_nonneg ‖v‖]

omit [NeZero (Module.finrank ℝ E)] in
theorem framedMetric_eq_pullback_normalCoordMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E)
    (hz : letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      z ∈ (framedExpDiffeo (I := I) Y.metric x).source) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    let L : E →L[Real] E :=
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap.comp
        (normalFrame (I := I) Y.metric x).toContinuousLinearMap
    framedMetric (I := I) Y.metric x z =
      pullbackForm
        (normalCoordMetric (I := I) Y x (L z), L) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let L : E →L[Real] E :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap.comp
      (normalFrame (I := I) Y.metric x).toContinuousLinearMap
  ext v w
  rw [pullbackForm_apply, framedMetric_apply, normalCoordMetric_apply,
    framedExp_apply, mfderiv_framedExp (I := I) Y.metric x hz]
  rfl

omit [NeZero (Module.finrank Real E)] in
theorem framedMetric_continuousAt_zero
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContinuousAt (framedMetric (I := I) Y.metric x) 0 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let L : E →L[Real] E :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap.comp
      (normalFrame (I := I) Y.metric x).toContinuousLinearMap
  let raw := normalCoordMetric (I := I) Y x
  let F : E → E →L[Real] E →L[Real] Real :=
    fun z => pullbackForm (raw (L z), L)
  have hzeroRaw :
      (0 : E) ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x) := by
    simpa only [Metric.mem_ball, dist_self] using
      expMapC2Radius_pos (I := I) Y.metric x
  have hraw : ContinuousAt raw 0 :=
    ((normalCoordMetric_contDiffOn_expBall (I := I) Y x).contDiffAt
      (Metric.isOpen_ball.mem_nhds hzeroRaw)).continuousAt
  have hrawL : ContinuousAt (fun z => raw (L z)) 0 := by
    change ContinuousAt (raw ∘ L) 0
    exact hraw.comp_of_eq L.continuous.continuousAt (map_zero L)
  have hpair : ContinuousAt (fun z => (raw (L z), L)) 0 :=
    hrawL.prodMk continuousAt_const
  have hF : ContinuousAt F 0 :=
    pullbackForm.contDiff.continuous.continuousAt.comp hpair
  have hev :
      framedMetric (I := I) Y.metric x =ᶠ[nhds (0 : E)] F := by
    filter_upwards [
      (framedExpDiffeo (I := I) Y.metric x).open_source.mem_nhds
        (zero_mem_framedExp_source (I := I) Y.metric x)] with z hz
    dsimp only [F]
    exact framedMetric_eq_pullback_normalCoordMetric (I := I) Y x z hz
  exact hF.congr hev.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_close_ball
    (f : E → E →L[Real] E →L[Real] Real)
    (hf : ContinuousAt f 0) :
    ∃ r : Real, 0 < r ∧ ∀ z ∈ Metric.ball (0 : E) r,
      ‖f z - f 0‖ ≤ 1 / 2 := by
  let : SeminormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let : SeminormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  obtain ⟨r, hr, hclose⟩ :=
    (Metric.continuousAt_iff (f := f) (a := (0 : E))).mp hf
      (1 / 2 : Real) (by norm_num)
  refine ⟨r, hr, fun z hz => ?_⟩
  have hnear := hclose (x := z) (Metric.mem_ball.mp hz)
  rw [dist_eq_norm] at hnear
  exact hnear.le

theorem exists_equiv_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ r : Real, 0 < r ∧ r ≤ expRadiusGp (I := I) Y.metric x ∧
      FramedNormalCoordMetricEquivOn (I := I) Y x
        (Metric.ball (0 : E) r) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let f := NormalCoordinates.framedMetric (I := I) Y.metric x
  have hcont : ContinuousAt f 0 := by
    simpa only [f] using framedMetric_continuousAt_zero (I := I) Y x
  obtain ⟨r₀, hr₀, hclose⟩ := exists_close_ball (E := E) f hcont
  let r := min r₀ (expRadiusGp (I := I) Y.metric x)
  refine ⟨r, lt_min hr₀ (expRadiusGp_pos (I := I) Y.metric x),
    min_le_right _ _, ?_⟩
  intro z hz v
  have hz₀ : z ∈ Metric.ball (0 : E) r₀ := by
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    exact lt_of_lt_of_le hz (min_le_left _ _)
  have hzero_eval : ∀ w : E, f 0 w w = ‖w‖ ^ 2 := by
    intro w
    calc
      f 0 w w =
          (innerSL Real : E →L[Real] E →L[Real] Real) w w :=
        congrArg (fun G => G w w) (framedMetric_zero (I := I) Y.metric x)
      _ = Inner.inner Real w w := rfl
      _ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  exact half_two_of_close (E := E) (f z) (f 0) (hclose z hz₀) hzero_eval v

theorem exists_equiv_radii
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    ∃ radius : (k : Nat) → (X.obj k).M → Real,
      ∀ (k : Nat) (x : (X.obj k).M),
        letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
        letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
        letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
        letI : T2Space (TangentBundle I (X.obj k).M) :=
          (X.obj k).t2TangentBundle
        0 < radius k x ∧
          radius k x ≤ expRadiusGp (I := I) (X.obj k).metric x ∧
      FramedNormalCoordMetricEquivOn (I := I) (X.obj k) x
            (Metric.ball (0 : E) (radius k x)) := by
  choose radius hpos hle hequiv using fun k x =>
    exists_equiv_ball (I := I) (X.obj k) x
  exact ⟨radius, fun k x => ⟨hpos k x, hle k x, hequiv k x⟩⟩

end HCGCompactness
end DifferentialGeometry
