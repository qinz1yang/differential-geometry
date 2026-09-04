import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.Intrinsic

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
structure NormalChartData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjectivityRadiusDecay (I := I) X) where
  ratio : Real
  ratio_pos : 0 < ratio
  ratio_mu0_le : ratio * hd.mu 0 ≤ 1 / 2
  chart : ∀ (k : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    NormalBallChart (I := I) x
  radius_eq : ∀ (k : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (chart k x).radius =
      ratio * hd.mu (hd.dist k x (X.obj k).basepoint)
  hom_eq : ∀ (k : Nat) (x : (X.obj k).M)
      (hcomplete : MetricComplete (I := I) (X.obj k)),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
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
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      with_unfolding_all
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w
    EqOn (chart k x).hom
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
      (Metric.ball (0 : E) (chart k x).radius)

namespace NormalChartData

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem radius_le_global
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : NormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (d.chart k x).radius ≤ d.ratio * hd.mu 0 := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  rw [d.radius_eq k x]
  exact mul_le_mul_of_nonneg_left
    (hd.mu_antitone (hreal.dist_nonneg k x (X.obj k).basepoint))
    d.ratio_pos.le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem metric_eq_intrinsic_frame_metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : NormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
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
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      with_unfolding_all
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w
    EqOn ((d.chart k x).metric (X.obj k).metric)
      (intrinsicFrameMetric (I := I) (X.obj k).metric hEnorm x)
      (Metric.ball (0 : E) (d.chart k x).radius) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
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
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj k).metric y w
  change EqOn ((d.chart k x).metric (X.obj k).metric)
    (intrinsicFrameMetric (I := I) (X.obj k).metric hEnorm x)
    (Metric.ball (0 : E) (d.chart k x).radius)
  intro z hz
  have hev : Filter.EventuallyEq (nhds z)
      (d.chart k x).hom
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x) :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
      fun q hq => d.hom_eq k x hcomplete hq
  have hD : mfderiv (modelWithCornersSelf Real E) I
      (d.chart k x).hom z =
      mfderiv (modelWithCornersSelf Real E) I
        (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x) z :=
    Filter.EventuallyEq.mfderiv_eq
      (I := modelWithCornersSelf Real E) (I' := I) hev
  ext v w
  rw [NormalBallChart.metric_apply, intrinsicFrameMetric_apply,
    d.hom_eq k x hcomplete hz, hD]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem mem_image_and_norm_inv_eq_riemannian_distance
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : NormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x y : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M => TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M => TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    Manifold.riemannianEDist I x y <
        ENNReal.ofReal (d.chart k x).radius →
      y ∈ (d.chart k x).hom '' Metric.ball (0 : E) (d.chart k x).radius ∧
        ‖(d.chart k x).inv y‖ =
          (Manifold.riemannianEDist I x y).toReal := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj k).M => TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : (z : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M => TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : ConnectedSpace (X.obj k).M := hconn
  let hEnorm : ∀ (z : (X.obj k).M) (w : TangentSpace I z),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner z w w)) := by
    intro z w
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj k).metric z w
  intro hy
  obtain ⟨v, hvExp, hvLen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) (X.obj k).metric hEnorm x y
  let z : E := (normalFrame (I := I) (X.obj k).metric x).symm v
  have hzFrame : normalFrame (I := I) (X.obj k).metric x z = v := by
    exact (normalFrame (I := I) (X.obj k).metric x).apply_symm_apply v
  have hzNorm :
      ‖z‖ = Real.sqrt ((X.obj k).metric.inner x v v) := by
    have h := normalFrame_sqrt (I := I) (X.obj k).metric x z
    rw [hzFrame] at h
    exact h.symm
  have hyFin : Manifold.riemannianEDist I x y ≠ (⊤ : ENNReal) :=
    ne_of_lt (hy.trans ENNReal.ofReal_lt_top)
  have hyReal :
      (Manifold.riemannianEDist I x y).toReal < (d.chart k x).radius :=
    (ENNReal.lt_ofReal_iff_toReal_lt hyFin).mp hy
  have hzBall : z ∈ Metric.ball (0 : E) (d.chart k x).radius := by
    rw [Metric.mem_ball, dist_zero_right, hzNorm, hvLen]
    exact hyReal
  have hmap : (d.chart k x).hom z = y := by
    calc
      (d.chart k x).hom z =
          intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x z :=
        d.hom_eq k x hcomplete hzBall
      _ = expMapIntrinsic (I := I) (X.obj k).metric hEnorm x
          (normalFrame (I := I) (X.obj k).metric x z) := by
        rw [intrinsicFrame_apply]
      _ = expMapIntrinsic (I := I) (X.obj k).metric hEnorm x v := by
        rw [hzFrame]
      _ = y := hvExp
  refine ⟨⟨z, hzBall, hmap⟩, ?_⟩
  change ‖(d.chart k x).hom.symm y‖ =
    (Manifold.riemannianEDist I x y).toReal
  have hinv : (d.chart k x).hom.symm y = z := by
    rw [← hmap]
    exact (d.chart k x).hom.left_inv
      ((d.chart k x).ball_subset hzBall)
  rw [hinv, hzNorm, hvLen]

end NormalChartData


structure BoundedGeometryNormalChartData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjectivityRadiusDecay (I := I) X)
    extends NormalChartData (I := I) X hd where
  metricC : Nat → Real
  metricC_nonneg : ∀ p : Nat, 0 ≤ metricC p
  metric_equiv : ∀ (k : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (chart k x).MetricEquivOn (X.obj k).metric
      (Metric.ball (0 : E) (chart k x).radius)
  metric_deriv : ∀ (k p : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (chart k x).MetricDerivBound (X.obj k).metric
      (Metric.ball (0 : E) (chart k x).radius) p (metricC p)

namespace BoundedGeometryNormalChartData

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (f : Nat → Nat) :
    BoundedGeometryNormalChartData (I := I) (X.subseq f) (hd.subseq f) where
  ratio := d.ratio
  ratio_pos := d.ratio_pos
  ratio_mu0_le := by
    simpa only [InjectivityRadiusDecay.mu, InjectivityRadiusDecay.subseq,
      BaseInjBound.subseq] using d.ratio_mu0_le
  chart := fun k x => d.chart (f k) x
  radius_eq := by
    intro k x
    simpa only [InjectivityRadiusDecay.mu, InjectivityRadiusDecay.subseq,
      BaseInjBound.subseq, PointedRiemannianSeq.subseq] using d.radius_eq (f k) x
  hom_eq := by
    intro k x hcomplete
    with_unfolding_all
      exact d.hom_eq (f k) x hcomplete
  metricC := d.metricC
  metricC_nonneg := d.metricC_nonneg
  metric_equiv := by
    intro k x
    with_unfolding_all
      exact d.metric_equiv (f k) x
  metric_deriv := by
    intro k p x
    with_unfolding_all
      exact d.metric_deriv (f k) p x

def chartMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat) (x : (X.obj k).M) :
    E → E →L[Real] E →L[Real] Real :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).metric (X.obj k).metric

def metricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (d.chart k x).MetricBounds (X.obj k).metric := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  exact
    { C := d.metricC
      C_nonneg := d.metricC_nonneg
      radius := (d.chart k x).radius
      radius_pos := (d.chart k x).radius_pos
      equiv := d.metric_equiv k x
      deriv := fun p => d.metric_deriv k p x }

def chartMap
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (x : (X.obj k).M) : E → (X.obj k).M :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).hom

def chartTransition
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (x y : (X.obj k).M) : E → E :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).transition (d.chart k y)

def chartOverlapOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (x y : (X.obj k).M) (U : Set E) : Prop :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).OverlapOn (d.chart k y) U

end BoundedGeometryNormalChartData

end CheegerGromovCompactness
end DifferentialGeometry
