import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.Defs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.JetBounds

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

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def IntrinsicBallChartData.toNormalChartData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    (d : IntrinsicBallChartData (I := I) X hd hcomplete hconn) :
    NormalChartData (I := I) X hd where
  ratio := d.ratio
  ratio_pos := d.ratio_pos
  ratio_mu0_le := d.ratio_mu0_le
  chart := fun k x => d.normalChart k x
  radius_eq := fun k x => d.normal_chart_radius k x
  hom_eq := fun k x hcomplete' => by
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
      MetricComplete.complete (I := I) (X.obj k) hcomplete'
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      with_unfolding_all
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w
    change EqOn (d.normalChart k x).hom
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
      (Metric.ball (0 : E) (d.normalChart k x).radius)
    intro z hz
    exact (d.chart k x).hom_eq hz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem IntrinsicBallChartData.normal_chart_metric_equiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    (d : IntrinsicBallChartData (I := I) X hd hcomplete hconn)
    (k : Nat) (x : (X.obj k).M) :
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
    (d.normalChart k x).MetricEquivOn (X.obj k).metric
      (Metric.ball (0 : E) (d.normalChart k x).radius) := by
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
  change (d.toNormalChartData.chart k x).MetricEquivOn (X.obj k).metric
    (Metric.ball (0 : E) (d.toNormalChartData.chart k x).radius)
  intro z hz v
  rw [(d.toNormalChartData.metric_eq_intrinsic_frame_metric k (hcomplete.complete k) x) hz]
  change z ∈ Metric.ball (0 : E) (d.normalChart k x).radius at hz
  rw [d.normal_chart_radius k x] at hz
  exact d.intr_equiv k x z hz v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem exists_intrinsic_ball_chart_data
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X)
    (hreal : hd.RealizesDistance) :
    Nonempty (IntrinsicBallChartData (I := I) X hd hcomplete hconn) := by
  obtain ⟨r₀, hr₀, hcontrol⟩ :=
    exists_intr_control (I := I) X hcomplete hconn hgeom
  let r₁ : Real := min r₀ 1
  have hr₁ : 0 < r₁ := lt_min hr₀ (by norm_num)
  have hr₁_le_r₀ : r₁ ≤ r₀ := min_le_left _ _
  have hr₁_le_one : r₁ ≤ 1 := min_le_right _ _
  refine ⟨{
    ratio := hd.normalChartRatio r₁
    ratio_pos := hd.normal_chart_ratio_pos hr₁
    ratio_mu0_le := hd.normal_chart_ratio_mul_mu_zero_le_half hr₁_le_one
    chart := ?_
    intr_equiv := ?_ }⟩
  · intro k x
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
      with_unfolding_all
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w
    let r : Real := hd.normalChartRadius r₁ k x
    have hr : 0 < r := hd.normal_chart_radius_pos hr₁ k x
    have hr₁' : r < r₁ := hd.normal_chart_radius_lt hreal hr₁ k x
    have hsub : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) r₀ :=
      Metric.ball_subset_ball (hr₁'.le.trans hr₁_le_r₀)
    have hloc :
        IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞
          (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
          (Metric.ball (0 : E) r) := by
      intro z
      exact (hcontrol k x).2 ⟨z, hsub z.2⟩
    have hdecay :
        HasInjRadiusAt (I := I) (X.obj k) x
          (hd.mu (hd.dist k x (X.obj k).basepoint)) := by
      simpa only [InjectivityRadiusDecay.mu] using hd.decay k x
    have hinj :
        InjOn (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
          (Metric.ball (0 : E) r) := by
      exact hdecay.injOn_ball (hcomplete.complete k)
        (hd.normal_chart_radius_lt_decay_scale r₁ k x)
    exact Classical.choice <| by
      simpa only [r, InjectivityRadiusDecay.normalChartRadius] using
        exists_intrinsic_ball_chart (I := I) (X.obj k).metric hEnorm x hloc hinj
  · intro k x
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
      with_unfolding_all
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w
    change ∀ z ∈ Metric.ball (0 : E) (hd.normalChartRadius r₁ k x), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
          intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ∧
        intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ≤
          2 * ‖v‖ ^ 2
    intro z hz v
    have hr₁' :
        hd.normalChartRadius r₁ k x < r₁ :=
      hd.normal_chart_radius_lt hreal hr₁ k x
    exact (hcontrol k x).1 z
      (Metric.ball_subset_ball (hr₁'.le.trans hr₁_le_r₀) hz) v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem exists_normal_chart_data
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X)
    (hreal : hd.RealizesDistance) :
    Nonempty (NormalChartData (I := I) X hd) := by
  obtain ⟨d⟩ :=
    exists_intrinsic_ball_chart_data (I := I) X hcomplete hconn hgeom hd hreal
  exact ⟨d.toNormalChartData⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_bounded_geometry_normal_data
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X)
    (hreal : hd.RealizesDistance) :
    Nonempty (BoundedGeometryNormalChartData (I := I) X hd) := by
  obtain ⟨d⟩ :=
    exists_intrinsic_ball_chart_data (I := I) X hcomplete hconn hgeom hd hreal
  let U : Real := d.ratio * hd.mu 0
  let metricC : Nat → Real := fun n =>
    ContinuousMultilinearMap.polarConst n *
      (2 * (2 ^ n * jacobiJetBound hgeom.C U 1 n ^ 2))
  refine ⟨{
    toNormalChartData := d.toNormalChartData
    metricC := metricC
    metricC_nonneg := ?_
    metric_equiv := ?_
    metric_deriv := ?_ }⟩
  · intro n
    exact mul_nonneg (ContinuousMultilinearMap.polarConst_nonneg n)
      (mul_nonneg (by norm_num)
        (mul_nonneg (by positivity) (sq_nonneg _)))
  · intro k x
    exact d.normal_chart_metric_equiv k x
  · intro k n x
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
      with_unfolding_all
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w
    let hPk : BoundedGeometry (I := I) (X.obj k) :=
      { C := hgeom.C
        nonneg := hgeom.nonneg
        bound := hgeom.bound k }
    refine NormalBallChart.MetricDerivBound.of_eq_on
      (g := (X.obj k).metric) Metric.isOpen_ball
      (d.toNormalChartData.metric_eq_intrinsic_frame_metric k (hcomplete.complete k) x) ?_
    intro z hz
    have hzU : ‖z‖ ≤ U := by
      have hzRadius :
          ‖z‖ < (d.toNormalChartData.chart k x).radius := by
        simpa [dist_zero_right] using Metric.mem_ball.mp hz
      exact hzRadius.le.trans
        (d.toNormalChartData.radius_le_global hreal k x)
    have hchartSmooth :
        ContDiffAt Real ∞
          ((d.toNormalChartData.chart k x).metric (X.obj k).metric) z :=
      ((d.toNormalChartData.chart k x).metric_cont_diff_on
        (X.obj k).metric Metric.isOpen_ball
        (d.toNormalChartData.chart k x).smooth_to).contDiffAt
          (Metric.isOpen_ball.mem_nhds hz)
    have heq :
        ((d.toNormalChartData.chart k x).metric (X.obj k).metric) =ᶠ[nhds z]
          intrFrameMetric (I := I) (X.obj k).metric hEnorm x :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
        fun q hq =>
          d.toNormalChartData.metric_eq_intrinsic_frame_metric k (hcomplete.complete k) x hq
    have hintrSmooth :
        ContDiffAt Real ∞
          (intrFrameMetric (I := I) (X.obj k).metric hEnorm x) z :=
      hchartSmooth.congr_of_eventuallyEq heq.symm
    exact intrinsic_frame_metric_iterated_fderiv_norm_le (I := I) (X.obj k)
      (hcomplete.complete k) (hconn k) hPk x z n U hzU hintrSmooth

end HCGCompactness
end DifferentialGeometry
