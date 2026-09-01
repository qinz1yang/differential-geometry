import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.IntrinsicGeometry

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

namespace InjectivityRadiusDecay

def normalChartRatio {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) (r₀ : Real) : Real :=
  min (1 / 2) (r₀ / (2 * hd.mu 0))

def normalChartRadius {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) (r₀ : Real)
    (k : Nat) (x : (X.obj k).M) : Real :=
  hd.normalChartRatio r₀ * hd.mu (hd.dist k x (X.obj k).basepoint)

omit [CompleteSpace E] in
theorem normal_chart_ratio_pos {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {r₀ : Real} (hr₀ : 0 < r₀) :
    0 < hd.normalChartRatio r₀ := by
  rw [normalChartRatio]
  exact lt_min (by norm_num)
    (div_pos hr₀ (mul_pos (by norm_num) (hd.mu_pos 0)))

omit [CompleteSpace E] in
theorem normal_chart_ratio_lt_one {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) (r₀ : Real) :
    hd.normalChartRatio r₀ < 1 :=
  lt_of_le_of_lt (min_le_left _ _) (by norm_num)

omit [CompleteSpace E] in
theorem normal_chart_ratio_mul_mu_zero_le_half
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {r₀ : Real} (hr₀ : r₀ ≤ 1) :
    hd.normalChartRatio r₀ * hd.mu 0 ≤ 1 / 2 := by
  have hmu₀ : 0 < hd.mu 0 := hd.mu_pos 0
  calc
    hd.normalChartRatio r₀ * hd.mu 0
        ≤ (r₀ / (2 * hd.mu 0)) * hd.mu 0 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hmu₀.le
    _ = r₀ / 2 := by field_simp [ne_of_gt hmu₀]
    _ ≤ 1 / 2 := by linarith

omit [CompleteSpace E] in
theorem normal_chart_radius_pos {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {r₀ : Real} (hr₀ : 0 < r₀)
    (k : Nat) (x : (X.obj k).M) :
    0 < hd.normalChartRadius r₀ k x :=
  mul_pos (hd.normal_chart_ratio_pos hr₀)
    (hd.mu_pos (hd.dist k x (X.obj k).basepoint))

omit [CompleteSpace E] in
theorem normal_chart_radius_lt {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) (hreal : hd.RealizesDistance)
    {r₀ : Real} (hr₀ : 0 < r₀) (k : Nat) (x : (X.obj k).M) :
    hd.normalChartRadius r₀ k x < r₀ := by
  have hmu₀ : 0 < hd.mu 0 := hd.mu_pos 0
  have hmu :
      hd.mu (hd.dist k x (X.obj k).basepoint) ≤ hd.mu 0 :=
    hd.mu_antitone (hreal.dist_nonneg k x (X.obj k).basepoint)
  calc
    hd.normalChartRadius r₀ k x
        ≤ hd.normalChartRatio r₀ * hd.mu 0 :=
      mul_le_mul_of_nonneg_left hmu (hd.normal_chart_ratio_pos hr₀).le
    _ ≤ (r₀ / (2 * hd.mu 0)) * hd.mu 0 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hmu₀.le
    _ = r₀ / 2 := by field_simp [ne_of_gt hmu₀]
    _ < r₀ := by linarith

omit [CompleteSpace E] in
theorem normal_chart_radius_lt_decay_scale {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) (r₀ : Real)
    (k : Nat) (x : (X.obj k).M) :
    hd.normalChartRadius r₀ k x <
      hd.mu (hd.dist k x (X.obj k).basepoint) := by
  rw [normalChartRadius]
  simpa only [one_mul] using
    mul_lt_mul_of_pos_right (hd.normal_chart_ratio_lt_one r₀)
      (hd.mu_pos (hd.dist k x (X.obj k).basepoint))

end InjectivityRadiusDecay

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
structure IntrinsicBallChartData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjectivityRadiusDecay (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) where
  ratio : Real
  ratio_pos : 0 < ratio
  ratio_mu0_le : ratio * hd.mu 0 ≤ 1 / 2
  chart : ∀ (k : Nat) (x : (X.obj k).M),
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
    IntrinsicBallChart (I := I) (X.obj k).metric hEnorm x
      (ratio * hd.mu (hd.dist k x (X.obj k).basepoint))
  intr_equiv : ∀ (k : Nat) (x : (X.obj k).M),
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
    ∀ z ∈ Metric.ball (0 : E)
        (ratio * hd.mu (hd.dist k x (X.obj k).basepoint)), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
          intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ∧
        intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ≤
          2 * ‖v‖ ^ 2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def IntrinsicBallChartData.normalChart
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
    NormalBallChart (I := I) x := by
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
  exact IntrinsicBallChart.toNormalBallChart
    (I := I) (X.obj k).metric hEnorm x (d.chart k x)
    (mul_pos d.ratio_pos
      (hd.mu_pos (hd.dist k x (X.obj k).basepoint)))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
@[simp] theorem IntrinsicBallChartData.normal_chart_radius
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
    (d.normalChart k x).radius =
      d.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) := by
  rfl

end HCGCompactness
end DifferentialGeometry
