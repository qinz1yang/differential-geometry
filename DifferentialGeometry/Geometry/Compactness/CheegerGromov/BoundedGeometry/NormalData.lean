import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoord


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Estimates.HigherMetricJet

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

namespace InjRadiusDecayInput

def normalChartRatio {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (r₀ : Real) : Real :=
  min (1 / 2) (r₀ / (2 * hd.mu 0))

def normalChartRadius {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (r₀ : Real)
    (k : Nat) (x : (X.obj k).M) : Real :=
  hd.normalChartRatio r₀ * hd.mu (hd.dist k x (X.obj k).basepoint)

omit [CompleteSpace E] in
theorem normal_chart_ratio_pos {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {r₀ : Real} (hr₀ : 0 < r₀) :
    0 < hd.normalChartRatio r₀ := by
  rw [normalChartRatio]
  exact lt_min (by norm_num)
    (div_pos hr₀ (mul_pos (by norm_num) (hd.mu_pos 0)))

omit [CompleteSpace E] in
theorem normal_chart_ratio_lt_one {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (r₀ : Real) :
    hd.normalChartRatio r₀ < 1 :=
  lt_of_le_of_lt (min_le_left _ _) (by norm_num)

omit [CompleteSpace E] in
theorem normal_chart_ratio_mul_mu_zero_le_half
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {r₀ : Real} (hr₀ : r₀ ≤ 1) :
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
    (hd : InjRadiusDecayInput (I := I) X) {r₀ : Real} (hr₀ : 0 < r₀)
    (k : Nat) (x : (X.obj k).M) :
    0 < hd.normalChartRadius r₀ k x :=
  mul_pos (hd.normal_chart_ratio_pos hr₀)
    (hd.mu_pos (hd.dist k x (X.obj k).basepoint))

omit [CompleteSpace E] in
theorem normal_chart_radius_lt {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (hreal : hd.RealizesEdist)
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
    (hd : InjRadiusDecayInput (I := I) X) (r₀ : Real)
    (k : Nat) (x : (X.obj k).M) :
    hd.normalChartRadius r₀ k x <
      hd.mu (hd.dist k x (X.obj k).basepoint) := by
  rw [normalChartRadius]
  simpa only [one_mul] using
    mul_lt_mul_of_pos_right (hd.normal_chart_ratio_lt_one r₀)
      (hd.mu_pos (hd.dist k x (X.obj k).basepoint))

end InjRadiusDecayInput

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
structure IntrinsicBallChartData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjRadiusDecayInput (I := I) X)
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
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
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
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    ∀ z ∈ Metric.ball (0 : E)
        (ratio * hd.mu (hd.dist k x (X.obj k).basepoint)), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
          intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ∧
        intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ≤
          2 * ‖v‖ ^ 2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
noncomputable def IntrinsicBallChartData.normalChart
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
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
    simpa using
      (tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj k).metric y w)
  exact IntrinsicBallChart.toNormalBallChart
    (I := I) (X.obj k).metric hEnorm x (d.chart k x)
    (mul_pos d.ratio_pos
      (hd.mu_pos (hd.dist k x (X.obj k).basepoint)))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
@[simp] theorem IntrinsicBallChartData.normal_chart_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
structure NormalChartData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjRadiusDecayInput (I := I) X) where
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
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    EqOn (chart k x).hom
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
      (Metric.ball (0 : E) (chart k x).radius)

namespace NormalChartData

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem radius_le_global
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : NormalChartData (I := I) X hd) (hreal : hd.RealizesEdist)
    (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (d.chart k x).radius ≤ d.ratio * hd.mu 0 := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  rw [d.radius_eq k x]
  exact mul_le_mul_of_nonneg_left
    (hd.mu_antitone (hreal.dist_nonneg k x (X.obj k).basepoint))
    d.ratio_pos.le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem metric_eq_intr
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
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
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    EqOn ((d.chart k x).metric (X.obj k).metric)
      (intrFrameMetric (I := I) (X.obj k).metric hEnorm x)
      (Metric.ball (0 : E) (d.chart k x).radius) := by
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
    simpa using
      (tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj k).metric y w)
  change EqOn ((d.chart k x).metric (X.obj k).metric)
    (intrFrameMetric (I := I) (X.obj k).metric hEnorm x)
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
  rw [NormalBallChart.metric_apply, intrFrameMetric_apply,
    d.hom_eq k x hcomplete hz, hD]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem readout_mem
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
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
  letI : ConnectedSpace (X.obj k).M := hconn
  let hEnorm : ∀ (z : (X.obj k).M) (w : TangentSpace I z),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner z w w)) := by
    intro z w
    simpa using
      (tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj k).metric z w)
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
        rw [intrFrame_apply]
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


structure BoundedGeometryNormalData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjRadiusDecayInput (I := I) X)
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

namespace BoundedGeometryNormalData

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (f : Nat → Nat) :
    BoundedGeometryNormalData (I := I) (X.subseq f) (hd.subseq f) where
  ratio := d.ratio
  ratio_pos := d.ratio_pos
  ratio_mu0_le := by
    simpa [InjRadiusDecayInput.subseq, InjRadiusDecayInput.mu] using
      d.ratio_mu0_le
  chart := fun k x => d.chart (f k) x
  radius_eq := by
    intro k x
    simpa [InjRadiusDecayInput.subseq, InjRadiusDecayInput.mu,
      PointedRiemannianSeq.subseq] using d.radius_eq (f k) x
  hom_eq := by
    intro k x hcomplete
    simpa [PointedRiemannianSeq.subseq] using
      d.hom_eq (f k) x hcomplete
  metricC := d.metricC
  metricC_nonneg := d.metricC_nonneg
  metric_equiv := by
    intro k x
    simpa [PointedRiemannianSeq.subseq] using d.metric_equiv (f k) x
  metric_deriv := by
    intro k p x
    simpa [PointedRiemannianSeq.subseq] using d.metric_deriv (f k) p x

def chartMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (k : Nat) (x : (X.obj k).M) :
    E → E →L[Real] E →L[Real] Real :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).metric (X.obj k).metric

def metricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (k : Nat) (x : (X.obj k).M) :
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
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (k : Nat)
    (x : (X.obj k).M) : E → (X.obj k).M :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).hom

def chartTransition
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (k : Nat)
    (x y : (X.obj k).M) : E → E :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).transition (d.chart k y)

def chartOverlapOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (k : Nat)
    (x y : (X.obj k).M) (U : Set E) : Prop :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).OverlapOn (d.chart k y) U

end BoundedGeometryNormalData

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
noncomputable def IntrinsicBallChartData.toChartData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
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
      MetricComplete.complete (I := I) (X.obj k) hcomplete'
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    change EqOn (d.normalChart k x).hom
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
      (Metric.ball (0 : E) (d.normalChart k x).radius)
    intro z hz
    exact (d.chart k x).hom_eq hz

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem IntrinsicBallChartData.normal_equiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
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
  change (d.toChartData.chart k x).MetricEquivOn (X.obj k).metric
    (Metric.ball (0 : E) (d.toChartData.chart k x).radius)
  intro z hz v
  rw [(d.toChartData.metric_eq_intr k (hcomplete.complete k) x) hz]
  change z ∈ Metric.ball (0 : E) (d.normalChart k x).radius at hz
  rw [d.normal_chart_radius k x] at hz
  exact d.intr_equiv k x z hz v

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem exists_intrinsic_ball_chart_data
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hd : InjRadiusDecayInput (I := I) X)
    (hreal : hd.RealizesEdist) :
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
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
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
      simpa only [InjRadiusDecayInput.mu] using hd.decay k x
    have hinj :
        InjOn (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
          (Metric.ball (0 : E) r) := by
      exact hdecay.injOn_ball (hcomplete.complete k)
        (hd.normal_chart_radius_lt_decay_scale r₁ k x)
    exact Classical.choice <| by
      simpa only [r, InjRadiusDecayInput.normalChartRadius] using
        exists_intrinsic_ball_chart (I := I) (X.obj k).metric hEnorm x hloc hinj
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
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem exists_normal_chart_data
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hd : InjRadiusDecayInput (I := I) X)
    (hreal : hd.RealizesEdist) :
    Nonempty (NormalChartData (I := I) X hd) := by
  obtain ⟨d⟩ :=
    exists_intrinsic_ball_chart_data (I := I) X hcomplete hconn hgeom hd hreal
  exact ⟨d.toChartData⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_bounded_geometry_normal_data
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hd : InjRadiusDecayInput (I := I) X)
    (hreal : hd.RealizesEdist) :
    Nonempty (BoundedGeometryNormalData (I := I) X hd) := by
  obtain ⟨d⟩ :=
    exists_intrinsic_ball_chart_data (I := I) X hcomplete hconn hgeom hd hreal
  let U : Real := d.ratio * hd.mu 0
  let metricC : Nat → Real := fun n =>
    ContinuousMultilinearMap.polarConst n *
      (2 * (2 ^ n * jetCap hgeom.C U 1 n ^ 2))
  refine ⟨{
    toNormalChartData := d.toChartData
    metricC := metricC
    metricC_nonneg := ?_
    metric_equiv := ?_
    metric_deriv := ?_ }⟩
  · intro n
    exact mul_nonneg (ContinuousMultilinearMap.polarConst_nonneg n)
      (mul_nonneg (by norm_num)
        (mul_nonneg (by positivity) (sq_nonneg _)))
  · intro k x
    exact d.normal_equiv k x
  · intro k n x
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
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    let hPk : BoundedGeometry (I := I) (X.obj k) :=
      { C := hgeom.C
        nonneg := hgeom.nonneg
        bound := hgeom.bound k }
    refine NormalBallChart.MetricDerivBound.of_eqOn
      (g := (X.obj k).metric) Metric.isOpen_ball
      (d.toChartData.metric_eq_intr k (hcomplete.complete k) x) ?_
    intro z hz
    have hzU : ‖z‖ ≤ U := by
      have hzRadius :
          ‖z‖ < (d.toChartData.chart k x).radius := by
        simpa [dist_zero_right] using Metric.mem_ball.mp hz
      exact hzRadius.le.trans
        (d.toChartData.radius_le_global hreal k x)
    have hchartSmooth :
        ContDiffAt Real ∞
          ((d.toChartData.chart k x).metric (X.obj k).metric) z :=
      ((d.toChartData.chart k x).metric_contDiffOn
        (X.obj k).metric Metric.isOpen_ball
        (d.toChartData.chart k x).smooth_to).contDiffAt
          (Metric.isOpen_ball.mem_nhds hz)
    have heq :
        ((d.toChartData.chart k x).metric (X.obj k).metric) =ᶠ[nhds z]
          intrFrameMetric (I := I) (X.obj k).metric hEnorm x :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
        fun q hq =>
          d.toChartData.metric_eq_intr k (hcomplete.complete k) x hq
    have hintrSmooth :
        ContDiffAt Real ∞
          (intrFrameMetric (I := I) (X.obj k).metric hEnorm x) z :=
      hchartSmooth.congr_of_eventuallyEq heq.symm
    exact intrMetric_deriv_le (I := I) (X.obj k)
      (hcomplete.complete k) (hconn k) hPk x z n U hzU hintrSmooth

end HCGCompactness
end DifferentialGeometry
