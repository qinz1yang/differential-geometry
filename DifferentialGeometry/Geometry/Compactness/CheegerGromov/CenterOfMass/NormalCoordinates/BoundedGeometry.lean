import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.Phase


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinates.Hessian
import DifferentialGeometry.Geometry.Exponential.NormalBallGeodesic

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold NNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.DivergenceTheorem

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace BoundedGeometryNormalChartData

omit [CompleteSpace E] in
theorem halfCage_ctrl
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {ρ : Real} {y pt : (X.obj k).M} :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    0 < ρ →
    ρ ≤ (d.chart k x).radius →
    max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2) →
    y ∈ (d.chart k x).restrictBall.target ∧
      ‖(d.chart k x).inv y‖ < ρ ∧
      riemannianEDist I y pt < ENNReal.ofReal ρ := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : (z : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  intro hρ hρChart hpairs
  have hy : riemannianEDist I x y < ENNReal.ofReal (ρ / 2) :=
    (le_max_left _ _).trans_lt hpairs
  have hpt : riemannianEDist I x pt < ENNReal.ofReal (ρ / 2) :=
    (le_max_right _ _).trans_lt hpairs
  have hyChart : riemannianEDist I x y <
      ENNReal.ofReal (d.chart k x).radius := by
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by nlinarith))
  have hread :=
    d.toNormalChartData.mem_image_and_norm_inv_eq_riemannian_distance k hcomplete hconn x y hyChart
  have hyFin : riemannianEDist I x y ≠ (⊤ : ENNReal) :=
    ne_of_lt (hy.trans ENNReal.ofReal_lt_top)
  have hyReal : (riemannianEDist I x y).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt hyFin).mp hy
  have hyTarget : y ∈ (d.chart k x).restrictBall.target := by
    exact hread.1
  have hyCoord : ‖(d.chart k x).inv y‖ < ρ := by
    rw [hread.2]
    nlinarith
  have hyx : riemannianEDist I y x < ENNReal.ofReal (ρ / 2) := by
    simpa only [riemannianEDist_comm] using hy
  have hsum : ENNReal.ofReal (ρ / 2) + ENNReal.ofReal (ρ / 2) =
      ENNReal.ofReal ρ := by
    calc
      ENNReal.ofReal (ρ / 2) + ENNReal.ofReal (ρ / 2) =
          ENNReal.ofReal (ρ / 2 + ρ / 2) :=
        (ENNReal.ofReal_add (by linarith) (by linarith)).symm
      _ = ENNReal.ofReal ρ := by ring_nf
  have hyp : riemannianEDist I y pt < ENNReal.ofReal ρ := by
    calc
      riemannianEDist I y pt ≤
          riemannianEDist I y x + riemannianEDist I x pt :=
        Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal (ρ / 2) + ENNReal.ofReal (ρ / 2) :=
        ENNReal.add_lt_add hyx hpt
      _ = ENNReal.ofReal ρ := hsum
  exact ⟨hyTarget, hyCoord, hyp⟩

omit [CompleteSpace E] in
theorem halfSq_inf
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    {pt : (X.obj k).M} :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ (d.chart k x).radius →
    ContMDiffOn I 𝓘(Real) ∞ (CenterOfMass.halfSqDist pt)
      {y : (X.obj k).M |
        max (riemannianEDist I x y) (riemannianEDist I x pt) <
          ENNReal.ofReal (ρ / 2)} := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : (z : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  intro hρ hρq hρChart
  apply IsNormalDiag.halfSq_inf_ctrl (I := I) (X.obj k)
    hcomplete hconn x (d.metricBounds k x) hq he hf
    hρ hρq
  · simpa only [metricBounds] using hρChart
  · intro y hy
    exact d.halfCage_ctrl k hcomplete hconn x hρ hρChart hy

omit [CompleteSpace E] in
theorem grad_half
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    {y pt : (X.obj k).M} :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ (d.chart k x).radius →
    max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2) →
    let B := IsNormalDiag.toBranch (I := I) (X.obj k)
      hcomplete hconn x hq he
    gradientFun (I := I) (X.obj k).metric
      (CenterOfMass.halfSqDist pt) y =
        -(show TangentSpace I y from (B.inv (y, pt)).snd) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : (z : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  intro hρ hρq hρChart hpairs
  let S : Set (X.obj k).M :=
    {z | max (riemannianEDist I x z) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2)}
  have hSopen : IsOpen S := by
    dsimp only [S]
    exact isOpen_lt
      ((continuous_riemannianEDist (I := I) (X.obj k).metric x).max
        continuous_const) continuous_const
  have hyS : y ∈ S := by
    change max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2)
    exact hpairs
  apply IsNormalDiag.grad_half_ctrl (I := I) (X.obj k)
    hcomplete hconn x (d.metricBounds k x) hq he hf
    hρ hρq
  · simpa only [metricBounds] using hρChart
  · exact hSopen
  · exact hyS
  · intro z hz
    exact d.halfCage_ctrl k hcomplete hconn x hρ hρChart hz

omit [CompleteSpace E] in
theorem hess_half
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    {y pt : (X.obj k).M} :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    ∀ v w : TangentSpace I y,
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ (d.chart k x).radius →
    max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2) →
    let B := IsNormalDiag.toBranch (I := I) (X.obj k)
      hcomplete hconn x hq he
    hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist pt) y v w =
      (X.obj k).metric.inner y
        ((LeviCivita (I := I) (X.obj k).metric).toFun
          (fun z =>
            -(show TangentSpace I z from (B.inv (z, pt)).snd))
          y v) w := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : (z : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  intro v w hρ hρq hρChart hpairs
  let S : Set (X.obj k).M :=
    {z | max (riemannianEDist I x z) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2)}
  have hSopen : IsOpen S := by
    dsimp only [S]
    exact isOpen_lt
      ((continuous_riemannianEDist (I := I) (X.obj k).metric x).max
        continuous_const) continuous_const
  have hyS : y ∈ S := by
    change max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2)
    exact hpairs
  apply IsNormalDiag.hess_half_ctrl (I := I) (X.obj k)
    hcomplete hconn x (d.metricBounds k x) hq he hf v w
    hρ hρq
  · simpa only [metricBounds] using hρChart
  · exact hSopen
  · exact hyS
  · intro z hz
    exact d.halfCage_ctrl k hcomplete hconn x hρ hρChart hz

theorem inv_cov
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    {z xi : E} (hw : (z, xi) ∈ e.target) (v : E) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    z ∈ Metric.ball (0 : E) ((d.chart k x).radius / 4) →
    let c := d.chart k x
    let B := IsNormalDiag.toBranch
      (I := I) (X.obj k) hcomplete hconn x hq he
    mfderiv 𝓘(Real, E) I c.hom z
        (((DifferentialGeometry.Geometry.Curvature.metricCov (I := 𝓘(Real, E)) (M := E)
          (c.totalMetric (X.obj k).metric)).toFun
          (fun u : E => (e.symm (u, xi)).2) z) v) =
      ((DifferentialGeometry.Geometry.Curvature.metricCov
        (I := I) (M := (X.obj k).M) (X.obj k).metric).toFun
        (fun y : (X.obj k).M =>
          (B.inv (y, c.hom xi)).snd)
        (c.hom z))
        (mfderiv 𝓘(Real, E) I c.hom z v) := by
  classical
  intro hzInner
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  dsimp only
  let c := d.chart k x
  let B := IsNormalDiag.toBranch
    (I := I) (X.obj k) hcomplete hconn x hq he
  let pt : (X.obj k).M := c.hom xi
  let y0 : (X.obj k).M := c.hom z
  let Vloc : E → E := fun u => (e.symm (u, xi)).2
  let VTan : (u : E) → TangentSpace 𝓘(Real, E) u := fun u => Vloc u
  let Zloc : (y : (X.obj k).M) → TangentSpace I y := fun y =>
    show TangentSpace I y from (B.inv (y, pt)).snd
  let Umod : Set E := (fun u : E => (u, xi)) ⁻¹' e.target
  have hUopen : IsOpen Umod :=
    e.open_target.preimage (continuous_id.prodMk continuous_const)
  have hzU : z ∈ Umod := hw
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ a ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) (X.obj k) x (e a) (c := c) =
        diagExp (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k))
          (normalTangent (I := I) (X.obj k) x a (c := c)) at heData
  have hpair : ContDiffOn Real ∞ (fun u : E => (u, xi)) Umod :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hsymm : ContDiffOn Real ∞
      (fun u : E => e.symm (u, xi)) Umod :=
    heData.2.2.2.2.1.comp hpair (fun u hu => hu)
  have hVfun : ContDiffOn Real ∞ Vloc Umod := by
    simpa only [Vloc] using hsymm.snd
  have hVsec : ContMDiffOn 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, E)) ∞
      (T% VTan) Umod := by
    exact contMDiffOn_vectorSpace_iff_contDiffOn.mpr
      (by simpa only [VTan] using hVfun)
  obtain ⟨Vexts, hVexts⟩ := exists_contMDiffSection_eqOn_nhd
    (I := 𝓘(Real, E)) (F := E) (V := TangentSpace 𝓘(Real, E))
    (n := (⊤ : ℕ∞)) (s := fun _ : Unit => VTan)
    (u := Umod) (p := z) (fun _ => hVsec) hUopen hzU
  let Vext : Cₛ^∞⟮𝓘(Real, E); E,
      (TangentSpace 𝓘(Real, E) : E → Type _)⟯ := Vexts ()
  have hVext : (fun u : E => Vext u) =ᶠ[nhds z] Vloc := by
    filter_upwards [hVexts] with u hu using hu ()
  let S : Set (X.obj k).M := (fun y : (X.obj k).M => (y, pt)) ⁻¹' B.dom
  have hSopen : IsOpen S := by
    change IsOpen ((fun y : (X.obj k).M => (y, pt)) ⁻¹' B.hom.target)
    exact B.hom.open_target.preimage (continuous_id.prodMk continuous_const)
  have htransport := IsNormalDiag.full_transport
    (I := I) (X.obj k) hcomplete hconn x hq he hf
  have hpairDom :
      normalPair (I := I) (X.obj k) x (z, xi) (c := c) ∈ B.dom := by
    rw [← htransport.2.1]
    exact ⟨(z, xi), hw, c.pairHome_apply (z, xi)⟩
  have hyS : y0 ∈ S := by
    change (y0, pt) ∈ B.dom
    with_unfolding_all
      exact hpairDom
  have hdom : ∀ y ∈ S, (y, pt) ∈ B.dom := fun _ hy => hy
  have hZsec : ContMDiffOn I I.tangent ∞ (T% Zloc) S :=
    B.inv_snd_inf hdom
  obtain ⟨Zexts, hZexts⟩ := exists_contMDiffSection_eqOn_nhd
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
    (s := fun _ : Unit => Zloc)
    (u := S) (p := y0) (fun _ => hZsec) hSopen hyS
  let Zext : Cₛ^∞⟮I; E,
      (TangentSpace I : (X.obj k).M → Type _)⟯ := Zexts ()
  have hZext : (fun y : (X.obj k).M => Zext y) =ᶠ[nhds y0] Zloc := by
    filter_upwards [hZexts] with y hy using hy ()
  have hzBall : z ∈ Metric.ball (0 : E) c.radius :=
    c.inner_subset hzInner
  have hfront : Filter.Tendsto c.hom (nhds z) (nhds y0) := by
    have hc : ContinuousAt c.hom z :=
      (c.smooth_to.contMDiffAt
        (Metric.isOpen_ball.mem_nhds hzBall)).continuousAt
    with_unfolding_all
      exact hc
  have hEq :
      (fun u : E => Zext (c.hom u)) =ᶠ[nhds z]
        (fun u : E => mfderiv 𝓘(Real, E) I c.hom u (Vext u)) := by
    filter_upwards [hfront.eventually hZext, hVext,
      hUopen.mem_nhds hzU] with u huZ huV huU
    rw [huZ, huV]
    have hInv := htransport.2.2 (u, xi) huU
    have hfst := IsNormalDiag.symm_fst_eq
      (I := I) (X.obj k) hcomplete hconn x he hf huU
    have hInv' :
        B.inv (normalPair (I := I) (X.obj k) x (u, xi) (c := c)) =
          normalTangent (I := I) (X.obj k) x
            (u, (e.symm (u, xi)).2) (c := c) := by
      rw [hInv]
      congr 1
      exact Prod.ext hfst rfl
    change
      (B.inv (normalPair (I := I) (X.obj k) x (u, xi) (c := c))).snd =
        mfderiv 𝓘(Real, E) I c.hom u (Vloc u)
    rw [hInv']
    rfl
  let zInner : c.inner := ⟨z, hzInner⟩
  have hmap := c.cov_map_germ (X.obj k).metric Vext Zext zInner v
    (by simpa only [zInner] using hEq)
  have hVlocAt : MDifferentiableAt 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, E)) (T% VTan) z :=
    (hVsec.contMDiffAt
      (hUopen.mem_nhds hzU)).mdifferentiableAt (by simp)
  have hVextAt : MDifferentiableAt 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, E))
      (T% fun u : E => Vext u) z :=
    Vext.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hsrc := DifferentialGeometry.Geometry.Curvature.metricCov_congr_nhds
    (I := 𝓘(Real, E)) (M := E) (c.totalMetric (X.obj k).metric)
    hVextAt hVlocAt hVext
  have hZlocAt : MDifferentiableAt I I.tangent (T% Zloc) y0 :=
    (hZsec.contMDiffAt
      (hSopen.mem_nhds hyS)).mdifferentiableAt (by simp)
  have hZextAt : MDifferentiableAt I I.tangent
      (T% fun y : (X.obj k).M => Zext y) y0 :=
    Zext.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have htgt := DifferentialGeometry.Geometry.Curvature.metricCov_congr_nhds
    (I := I) (M := (X.obj k).M) (X.obj k).metric
    hZextAt hZlocAt hZext
  rw [hsrc, htgt] at hmap
  simpa only [c, B, Vloc, VTan, Zloc, y0, pt, zInner] using hmap

theorem hess_coord
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    {z xi : E} (hw : (z, xi) ∈ e.target) (v w : E) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    let c := d.chart k x
    z ∈ Metric.ball (0 : E) (c.radius / 4) →
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ c.radius →
    max (riemannianEDist I x (c.hom z))
        (riemannianEDist I x (c.hom xi)) <
      ENNReal.ofReal (ρ / 2) →
    let dHom := mfderiv 𝓘(Real, E) I c.hom z
    hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist (c.hom xi)) (c.hom z)
        (dHom v) (dHom w) =
      -c.metric (X.obj k).metric z
        (((DifferentialGeometry.Geometry.Curvature.metricCov
          (I := 𝓘(Real, E)) (M := E)
          (c.totalMetric (X.obj k).metric)).toFun
          (fun u : E => (e.symm (u, xi)).2) z) v) w := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  dsimp only
  intro hzInner hρ hρq hρChart hpairs
  let c := d.chart k x
  let B := IsNormalDiag.toBranch
    (I := I) (X.obj k) hcomplete hconn x hq he
  let pt : (X.obj k).M := c.hom xi
  let y0 : (X.obj k).M := c.hom z
  let dHom := mfderiv 𝓘(Real, E) I c.hom z
  let Z : (y : (X.obj k).M) → TangentSpace I y := fun y =>
    show TangentSpace I y from (B.inv (y, pt)).snd
  let S : Set (X.obj k).M :=
    {y | max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2)}
  have hSopen : IsOpen S := by
    dsimp only [S]
    exact isOpen_lt
      ((continuous_riemannianEDist (I := I) (X.obj k).metric x).max
        continuous_const) continuous_const
  have hyS : y0 ∈ S := by
    change max (riemannianEDist I x y0) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2)
    with_unfolding_all
      exact hpairs
  have hdom : ∀ y ∈ S, (y, pt) ∈ B.dom := by
    intro y hy
    have hctrl := d.halfCage_ctrl k hcomplete hconn x hρ hρChart
      (by
        change max (riemannianEDist I x y) (riemannianEDist I x pt) <
          ENNReal.ofReal (ρ / 2) at hy
        exact hy)
    exact
      (IsNormalDiag.inv_is_min_ctrl (I := I) (X.obj k)
        hcomplete hconn x (d.metricBounds k x) hq he hf
        hρ hρq (by simpa only [metricBounds] using hρChart)
        hctrl.1 hctrl.2.1 hctrl.2.2).choose_spec.1
  have hZat : MDifferentiableAt I I.tangent (T% Z) y0 :=
    ((B.inv_snd_inf hdom).contMDiffAt
      (hSopen.mem_nhds hyS)).mdifferentiableAt (by simp)
  have hneg :
      (LeviCivita (I := I) (X.obj k).metric).toFun
          (fun y => -Z y) y0 (dHom v) =
        -(LeviCivita (I := I) (X.obj k).metric).toFun
          Z y0 (dHom v) := by
    have hsmul :=
      (LeviCivita (I := I) (X.obj k).metric).isCovariantDerivativeOnUniv.smul_const
        (-1 : Real) hZat
    have happ := congrArg (fun A => A (dHom v)) hsmul
    have hfun : (fun y => -Z y) = -Z := by
      funext y
      rfl
    rw [hfun]
    simpa only [Pi.smul_apply, neg_one_smul, neg_apply] using happ
  have hhess := d.hess_half k hcomplete hconn x hq he hf
    (dHom v) (dHom w) hρ hρq hρChart
    (by simpa only [y0, pt] using hpairs)
  have hcov := d.inv_cov k hcomplete hconn x hq he hf hw v hzInner
  have hcov' :
      (LeviCivita (I := I) (X.obj k).metric).toFun Z y0 (dHom v) =
        dHom (((DifferentialGeometry.Geometry.Curvature.metricCov
          (I := 𝓘(Real, E)) (M := E)
          (c.totalMetric (X.obj k).metric)).toFun
          (fun u : E => (e.symm (u, xi)).2) z) v) := by
    simpa only [c, B, Z, y0, pt, dHom, LeviCivita,
      DifferentialGeometry.Geometry.Curvature.metricCov] using hcov.symm
  calc
    hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist pt) y0 (dHom v) (dHom w) =
      (X.obj k).metric.inner y0
        ((LeviCivita (I := I) (X.obj k).metric).toFun
          (fun y => -Z y) y0 (dHom v)) (dHom w) := by
            simpa only [B, Z, y0, pt] using hhess
    _ = (X.obj k).metric.inner y0
        (-(LeviCivita (I := I) (X.obj k).metric).toFun
          Z y0 (dHom v)) (dHom w) := by rw [hneg]
    _ = -((X.obj k).metric.inner y0
        ((LeviCivita (I := I) (X.obj k).metric).toFun
          Z y0 (dHom v)) (dHom w)) := by
            rw [ContinuousLinearMap.map_neg, neg_apply]
    _ = -((X.obj k).metric.inner y0
        (dHom (((DifferentialGeometry.Geometry.Curvature.metricCov
          (I := 𝓘(Real, E)) (M := E)
          (c.totalMetric (X.obj k).metric)).toFun
          (fun u : E => (e.symm (u, xi)).2) z) v)) (dHom w)) := by
            rw [hcov']
    _ = -c.metric (X.obj k).metric z
        (((DifferentialGeometry.Geometry.Curvature.metricCov
          (I := 𝓘(Real, E)) (M := E)
          (c.totalMetric (X.obj k).metric)).toFun
          (fun u : E => (e.symm (u, xi)).2) z) v) w := by
            with_unfolding_all
              exact congrArg (fun s : Real => -s)
                (c.metric_apply (X.obj k).metric z
                  (((DifferentialGeometry.Geometry.Curvature.metricCov
                    (I := 𝓘(Real, E)) (M := E)
                    (c.totalMetric (X.obj k).metric)).toFun
                    (fun u : E => (e.symm (u, xi)).2) z) v) w).symm

theorem cov_expand
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    {z xi : E} (hw : (z, xi) ∈ e.target) (v : E) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    ∀ hzInner : z ∈ Metric.ball (0 : E) ((d.chart k x).radius / 4),
    let c := d.chart k x
    let hzMetric := c.inner_subset hzInner
    ((DifferentialGeometry.Geometry.Curvature.metricCov (I := 𝓘(Real, E)) (M := E)
        (c.totalMetric (X.obj k).metric)).toFun
        (fun u : E => (e.symm (u, xi)).2) z) v =
      fderiv Real (fun u : E => (e.symm (u, xi)).2) z v +
        MetricKoszul.koszulVec
          ((d.metricBounds k x).equiv.coercive
            (X.obj k).metric hzMetric)
          (fderiv Real (c.metric (X.obj k).metric) z)
          v (e.symm (z, xi)).2 := by
  classical
  intro hzInner
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  dsimp only
  let c := d.chart k x
  let V : E → E := fun u => (e.symm (u, xi)).2
  let VTan : (u : E) → TangentSpace 𝓘(Real, E) u := fun u => V u
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ a ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) (X.obj k) x (e a) (c := c) =
        diagExp (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k))
          (normalTangent (I := I) (X.obj k) x a (c := c)) at heData
  have hInvAt : ContDiffAt Real ∞
      (e.symm : E × E → E × E) (z, xi) :=
    (heData.2.2.2.2.1 (z, xi) hw).contDiffAt
      (e.open_target.mem_nhds hw)
  have hpair : ContDiffAt Real ∞ (fun u : E => (u, xi)) z :=
    (contDiff_id.prodMk contDiff_const).contDiffAt
  have hVcd : ContDiffAt Real ∞ V z := by
    with_unfolding_all
      exact (hInvAt.comp z hpair).snd
  have hVmd : MDifferentiableAt 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, E)) (T% VTan) z :=
    (contMDiffAt_vectorSpace_iff_contDiffAt.mpr
      (by simpa only [VTan] using hVcd)).mdifferentiableAt (by simp)
  have hzMetric : z ∈ Metric.ball (0 : E) c.radius :=
    c.inner_subset hzInner
  have hcov := c.total_cov_fderiv (X.obj k).metric z hzInner
    ((d.metricBounds k x).equiv.coercive
      (X.obj k).metric hzMetric) V hVmd v
  with_unfolding_all
    exact hcov

theorem hess_lower
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q eta : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    {z xi : E} (hw : (z, xi) ∈ e.target) (v : E) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    let c := d.chart k x
    z ∈ Metric.ball (0 : E) (c.radius / 4) →
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ c.radius →
    max (riemannianEDist I x (c.hom z))
        (riemannianEDist I x (c.hom xi)) <
      ENNReal.ofReal (ρ / 2) →
    let dHom := mfderiv 𝓘(Real, E) I c.hom z
    (1 - 4 * (eta : Real) - 12 * d.metricC 1 * (q : Real)) *
        c.metric (X.obj k).metric z v v ≤
      hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist (c.hom xi)) (c.hom z)
        (dHom v) (dHom v) := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  dsimp only
  intro hzInner hρ hρq hρChart hpairs
  let c := d.chart k x
  let V : E → E := fun u ↦ (e.symm (u, xi)).2
  let A : E →L[Real] E := fderiv Real V z
  have hzMetric : z ∈ Metric.ball (0 : E) c.radius :=
    c.inner_subset hzInner
  let K : E := MetricKoszul.koszulVec
    ((d.metricBounds k x).equiv.coercive
      (X.obj k).metric hzMetric)
    (fderiv Real (c.metric (X.obj k).metric) z)
    v (e.symm (z, xi)).2
  let g : E →L[Real] E →L[Real] Real :=
    c.metric (X.obj k).metric z
  let dHom := mfderiv 𝓘(Real, E) I c.hom z
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ a ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) (X.obj k) x (e a) (c := c) =
        diagExp (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k))
          (normalTangent (I := I) (X.obj k) x a (c := c)) at heData
  have hInvDiff : DifferentiableAt Real
      (e.symm : E × E → E × E) (z, xi) :=
    ((heData.2.2.2.2.1 (z, xi) hw).contDiffAt
      (e.open_target.mem_nhds hw)).differentiableAt (by simp)
  have hAop : ‖A + ContinuousLinearMap.id Real E‖ ≤ (eta : Real) := by
    simpa only [A, V] using PhaseFlow.invVel_fderiv_le happrox
      (e.open_target.mem_nhds hw) hInvDiff
  have hAeval :
      ‖(A + ContinuousLinearMap.id Real E) v‖ ≤
        (eta : Real) * ‖v‖ :=
    (A + ContinuousLinearMap.id Real E).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right hAop (norm_nonneg v))
  have hpre : e.symm (z, xi) ∈ Metric.ball (0 : E × E) q := by
    rw [← heData.1]
    exact e.map_target hw
  have hpreNorm : ‖e.symm (z, xi)‖ < (q : Real) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hpre
  have hVnorm : ‖(e.symm (z, xi)).2‖ ≤ (q : Real) :=
    (norm_snd_le (e.symm (z, xi))).trans hpreNorm.le
  have hKnorm : ‖K‖ ≤ 3 * d.metricC 1 * ‖v‖ * (q : Real) := by
    refine ((d.metricBounds k x).koszul_vec_norm_le
      (X.obj k).metric hzMetric v (e.symm (z, xi)).2).trans ?_
    exact mul_le_mul_of_nonneg_left hVnorm
      (mul_nonneg
        (mul_nonneg (by norm_num) (d.metricC_nonneg 1)) (norm_nonneg v))
  have hquad := (d.metricBounds k x).equiv z hzMetric v
  have hg0 : 0 ≤ g v v := by
    dsimp only [g]
    exact (mul_nonneg (by norm_num) (sq_nonneg ‖v‖)).trans hquad.1
  have hvSq : ‖v‖ ^ 2 ≤ 2 * g v v := by
    dsimp only [g]
    nlinarith [hquad.1]
  have hAabs :
      |g ((A + ContinuousLinearMap.id Real E) v) v| ≤
        4 * (eta : Real) * g v v := by
    calc
      |g ((A + ContinuousLinearMap.id Real E) v) v| ≤
          2 * ‖(A + ContinuousLinearMap.id Real E) v‖ * ‖v‖ := by
            dsimp only [g]
            exact (d.metricBounds k x).equiv.abs_apply_le
              (X.obj k).metric hzMetric _ _
      _ ≤ 2 * ((eta : Real) * ‖v‖) * ‖v‖ := by
        gcongr
      _ ≤ 4 * (eta : Real) * g v v := by
        have heta0 : 0 ≤ (eta : Real) := NNReal.coe_nonneg eta
        nlinarith
  have hKabs :
      |g K v| ≤ 12 * d.metricC 1 * (q : Real) * g v v := by
    calc
      |g K v| ≤ 2 * ‖K‖ * ‖v‖ := by
        dsimp only [g]
        exact (d.metricBounds k x).equiv.abs_apply_le
          (X.obj k).metric hzMetric _ _
      _ ≤ 2 * (3 * d.metricC 1 * ‖v‖ * (q : Real)) * ‖v‖ := by
        gcongr
      _ ≤ 12 * d.metricC 1 * (q : Real) * g v v := by
        have hC0 := d.metricC_nonneg 1
        have hq0 : 0 ≤ (q : Real) := NNReal.coe_nonneg q
        calc
          2 * (3 * d.metricC 1 * ‖v‖ * (q : Real)) * ‖v‖ =
              6 * d.metricC 1 * (q : Real) * ‖v‖ ^ 2 := by ring
          _ ≤ 6 * d.metricC 1 * (q : Real) * (2 * g v v) := by
            gcongr
          _ = 12 * d.metricC 1 * (q : Real) * g v v := by ring
  have hdecomp :
      -g (A v + K) v =
        g v v - g ((A + ContinuousLinearMap.id Real E) v) v - g K v := by
    have hAg : g (A v) v =
        g ((A + ContinuousLinearMap.id Real E) v) v - g v v := by
      have hsum :
          (A + ContinuousLinearMap.id Real E) v = A v + v := by
        simp only [add_apply,
          ContinuousLinearMap.id_apply]
      rw [hsum, map_add, add_apply]
      ring
    calc
      -g (A v + K) v = -(g (A v) v + g K v) := by
        rw [map_add, add_apply]
      _ = -(g ((A + ContinuousLinearMap.id Real E) v) v -
          g v v + g K v) := by rw [hAg]
      _ = g v v - g ((A + ContinuousLinearMap.id Real E) v) v -
          g K v := by ring
  have hhess := d.hess_coord k hcomplete hconn x hq he hf hw v v
    hzInner hρ hρq hρChart hpairs
  have hcov := d.cov_expand k hcomplete hconn x he hw v hzInner
  have hhess' :
      hessFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist (c.hom xi)) (c.hom z)
          (dHom v) (dHom v) =
        -g (A v + K) v := by
    rw [hhess, hcov]
  rw [hhess', hdecomp]
  have hAupper : g ((A + ContinuousLinearMap.id Real E) v) v ≤
      4 * (eta : Real) * g v v := (le_abs_self _).trans hAabs
  have hKupper : g K v ≤
      12 * d.metricC 1 * (q : Real) * g v v :=
    (le_abs_self _).trans hKabs
  nlinarith

theorem hess_sixth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q eta : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < (1 / 24 : NNReal))
    (hqAcc : 3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real))
    {z xi : E} (hw : (z, xi) ∈ e.target) (v : E) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    let c := d.chart k x
    z ∈ Metric.ball (0 : E) (c.radius / 4) →
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ c.radius →
    max (riemannianEDist I x (c.hom z))
        (riemannianEDist I x (c.hom xi)) <
      ENNReal.ofReal (ρ / 2) →
    let dHom := mfderiv 𝓘(Real, E) I c.hom z
    (1 / 6 : Real) * c.metric (X.obj k).metric z v v ≤
      hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist (c.hom xi)) (c.hom z)
        (dHom v) (dHom v) := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  dsimp only
  intro hzInner hρ hρq hρChart hpairs
  have hlower := d.hess_lower k hcomplete hconn x hq he hf happrox
    hw v hzInner hρ hρq hρChart hpairs
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hqCoef : 12 * d.metricC 1 * (q : Real) ≤ (2 / 3 : Real) := by
    refine le_of_mul_le_mul_right ?_ hqReal
    nlinarith [hqAcc]
  have hetaReal : (eta : Real) < (1 / 24 : Real) := by
    exact_mod_cast heta
  have hcoef : (1 / 6 : Real) ≤
      1 - 4 * (eta : Real) - 12 * d.metricC 1 * (q : Real) := by
    nlinarith
  let c := d.chart k x
  have hzMetric : z ∈ Metric.ball (0 : E) c.radius :=
    c.inner_subset hzInner
  have hquad := (d.metricBounds k x).equiv z hzMetric v
  have hg0 : 0 ≤ c.metric (X.obj k).metric z v v :=
    (mul_nonneg (by norm_num) (sq_nonneg ‖v‖)).trans hquad.1
  exact (mul_le_mul_of_nonneg_right hcoef hg0).trans hlower

theorem hess_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q eta : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < (1 / 24 : NNReal))
    (hqAcc : 3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real)) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    let c := d.chart k x
    ρ ≤ c.radius / 4 →
    0 < ρ →
    2 * ρ < (q : Real) →
    ∀ {y pt : (X.obj k).M},
      max (riemannianEDist I x y) (riemannianEDist I x pt) <
          ENNReal.ofReal (ρ / 2) →
      ∀ {v : TangentSpace I y}, v ≠ 0 →
        0 < hessFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist pt) y v v := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  dsimp only
  intro hρInner hρ hρq y pt hpairs v hv
  let c := d.chart k x
  have hρChart : ρ ≤ c.radius := by
    have hc : c.radius / 4 ≤ c.radius := by
      nlinarith [c.radius_pos]
    exact hρInner.trans hc
  have hyCtrl := d.halfCage_ctrl k hcomplete hconn x
    hρ hρChart hpairs
  have hpairs' :
      max (riemannianEDist I x pt) (riemannianEDist I x y) <
        ENNReal.ofReal (ρ / 2) := by
    simpa only [max_comm] using hpairs
  have hptCtrl := d.halfCage_ctrl k hcomplete hconn x
    hρ hρChart hpairs'
  let z : E := c.inv y
  let xi : E := c.inv pt
  have hzInner : z ∈ Metric.ball (0 : E) (c.radius / 4) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hyCtrl.2.1.trans_le hρInner
  have hzBall : z ∈ Metric.ball (0 : E) c.radius := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hyCtrl.2.1.trans_le hρChart
  have hdom :
      (y, pt) ∈ (IsNormalDiag.toBranch
        (I := I) (X.obj k) hcomplete hconn x hq he).dom :=
    (IsNormalDiag.inv_is_min_ctrl (I := I) (X.obj k)
      hcomplete hconn x (d.metricBounds k x) hq he hf
      hρ hρq (by simpa only [metricBounds] using hρChart)
      hyCtrl.1 hyCtrl.2.1 hyCtrl.2.2).choose_spec.1
  have hw : (z, xi) ∈ e.target := by
    simpa only [z, xi, c] using
      IsNormalDiag.target_of_inv_dom (I := I) (X.obj k)
        hcomplete hconn x hq he hyCtrl.1 hptCtrl.1 hdom
  have hzSrc : z ∈ c.hom.source :=
    c.ball_subset hzBall
  let hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I 1 c.hom z :=
    PartialDiffeomorph.isLocalDiffeomorphAt
      (I := 𝓘(Real, E)) (J := I) (n := 1) c.hom hzSrc
  let dHomEquiv : E ≃L[Real] TangentSpace I (c.hom z) :=
    hloc.mfderivToContinuousLinearEquiv (by norm_num)
  let u : E := dHomEquiv.symm v
  have hu : u ≠ 0 := by
    intro hu0
    apply hv
    change dHomEquiv.symm v = 0 at hu0
    have hzero := congrArg (fun w => dHomEquiv w) hu0
    have happly : dHomEquiv (dHomEquiv.symm v) = v :=
      dHomEquiv.apply_symm_apply v
    have hzero' : dHomEquiv (dHomEquiv.symm v) = 0 :=
      hzero.trans (map_zero dHomEquiv)
    exact happly.symm.trans hzero'
  have hdHom : mfderiv 𝓘(Real, E) I c.hom z u = v := by
    have hcoe := hloc.mfderivToContinuousLinearEquiv_coe (by norm_num)
    change (mfderiv 𝓘(Real, E) I c.hom z) u = v
    rw [← hcoe, ContinuousLinearEquiv.coe_coe]
    change dHomEquiv (dHomEquiv.symm v) = v
    exact dHomEquiv.apply_symm_apply v
  have hyDecode : c.hom z = y := by
    with_unfolding_all
      exact c.restrictBall.right_inv hyCtrl.1
  have hptDecode : c.hom xi = pt := by
    with_unfolding_all
      exact c.restrictBall.right_inv hptCtrl.1
  have hmetric := (d.metricBounds k x).equiv z hzBall u
  have hnorm : 0 < ‖u‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hgpos : 0 < c.metric (X.obj k).metric z u u := by
    nlinarith [hmetric.1]
  have hpairsModel :
      max (riemannianEDist I x (c.hom z))
          (riemannianEDist I x (c.hom xi)) <
        ENNReal.ofReal (ρ / 2) := by
    simpa only [hyDecode, hptDecode] using hpairs
  have hhess := d.hess_sixth k hcomplete hconn x hq he hf
    happrox heta hqAcc hw u hzInner hρ hρq hρChart hpairsModel
  dsimp only at hhess
  have hdHom' :
      mfderiv 𝓘(Real, E) I (d.chart k x).hom z u = v := by
    simpa only [c] using hdHom
  have hyDecode' : (d.chart k x).hom z = y := by
    simpa only [c] using hyDecode
  rw [hdHom', hyDecode'] at hhess
  have hhess' : (1 / 6 : Real) *
        c.metric (X.obj k).metric z u u ≤
      hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist pt) y v v := by
    simpa only [c, hptDecode] using hhess
  nlinarith

omit [CompleteSpace E] in
theorem center_of_mass_normal_coordinate_data
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    {ι : Type} [Fintype ι] (mu : ι → Real)
    (pts : ι → (X.obj k).M)
    (join : (X.obj k).M → (X.obj k).M → Real → (X.obj k).M)
    (p : (X.obj k).M) (r : Real) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    ∀ h : CenterInput (I := I) (X.obj k).metric mu pts join p r,
      0 < ρ →
      2 * ρ < (q : Real) →
      ρ ≤ (d.chart k x).radius →
      let y := centerOfMass (I := I) (X.obj k).metric mu pts join p r h
      (∀ i, max (riemannianEDist I x y)
          (riemannianEDist I x (pts i)) < ENNReal.ofReal (ρ / 2)) →
      let c := d.chart k x
      let B := IsNormalDiag.toBranch
        (I := I) (X.obj k) hcomplete hconn x hq he
      let z := c.inv y
      let xi : ι → E := fun i => c.inv (pts i)
      y ∈ c.restrictBall.target ∧
        z ∈ Metric.ball (0 : E) c.radius ∧
        (∀ i, xi i ∈ Metric.ball (0 : E) c.radius) ∧
        (∀ i, (z, xi i) ∈ e.target) ∧
        (∀ i, (c.hom z, c.hom (xi i)) ∈ B.chartReadDom c) ∧
        chartCmEqnC (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k)) x c B z (mu, xi) = 0 := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : (z : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  intro h hρ hρq hρChart
  dsimp only
  let y := centerOfMass (I := I) (X.obj k).metric mu pts join p r h
  intro hpairs
  let c := d.chart k x
  let B := IsNormalDiag.toBranch
    (I := I) (X.obj k) hcomplete hconn x hq he
  let z := c.inv y
  let xi : ι → E := fun i => c.inv (pts i)
  obtain ⟨i₀, _hi₀⟩ := h.μ_pos
  have hyCtrl :
      y ∈ c.restrictBall.target ∧ ‖c.inv y‖ < ρ ∧
        riemannianEDist I y (pts i₀) < ENNReal.ofReal ρ := by
    simpa only [c] using
      d.halfCage_ctrl k hcomplete hconn x hρ hρChart (hpairs i₀)
  have hptCtrl (i : ι) :
      pts i ∈ c.restrictBall.target ∧ ‖c.inv (pts i)‖ < ρ ∧
        riemannianEDist I (pts i) y < ENNReal.ofReal ρ := by
    have hpairs' :
        max (riemannianEDist I x (pts i)) (riemannianEDist I x y) <
          ENNReal.ofReal (ρ / 2) := by
      simpa only [max_comm] using hpairs i
    simpa only [c] using
      d.halfCage_ctrl k hcomplete hconn x hρ hρChart hpairs'
  have hzBall : z ∈ Metric.ball (0 : E) c.radius := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hyCtrl.2.1.trans_le hρChart
  have hxiBall (i : ι) : xi i ∈ Metric.ball (0 : E) c.radius := by
    rw [Metric.mem_ball, dist_zero_right]
    exact (hptCtrl i).2.1.trans_le hρChart
  have hdiff (i : ι) : MDifferentiableAt I 𝓘(Real, Real)
      (CenterOfMass.halfSqDist (pts i)) y := by
    let S : Set (X.obj k).M :=
      {w | max (riemannianEDist I x w)
        (riemannianEDist I x (pts i)) < ENNReal.ofReal (ρ / 2)}
    have hSopen : IsOpen S := by
      dsimp only [S]
      exact isOpen_lt
        ((continuous_riemannianEDist (I := I) (X.obj k).metric x).max
          continuous_const) continuous_const
    have hsmooth : ContMDiffOn I 𝓘(Real) ∞
        (CenterOfMass.halfSqDist (pts i)) S := by
      simpa only [S] using
        d.halfSq_inf k hcomplete hconn x hq he hf hρ hρq hρChart
    have hyS : y ∈ S := by
      change max (riemannianEDist I x y) (riemannianEDist I x (pts i)) <
        ENNReal.ofReal (ρ / 2)
      exact hpairs i
    exact (hsmooth.contMDiffAt
      (hSopen.mem_nhds hyS)).mdifferentiableAt (by simp)
  have hgrad (i : ι) :
      gradientFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist (pts i)) y =
        -(show TangentSpace I y from (B.inv (y, pts i)).snd) := by
    simpa only [B, y] using
      d.grad_half k hcomplete hconn x hq he hf hρ hρq hρChart
        (hpairs i)
  have hsum : ∑ i : ι, mu i •
      (show TangentSpace I y from (B.inv (y, pts i)).snd) = 0 := by
    simpa only [y] using
      centerOfMass.invB_eqn (I := I) h
        (fun i => show TangentSpace I y from (B.inv (y, pts i)).snd)
        hdiff hgrad
  have hdom (i : ι) : (y, pts i) ∈ B.dom := by
    have hctrl := d.halfCage_ctrl k hcomplete hconn x
      hρ hρChart (hpairs i)
    exact
      (IsNormalDiag.inv_is_min_ctrl (I := I) (X.obj k)
        hcomplete hconn x (d.metricBounds k x) hq he hf
        hρ hρq (by simpa only [metricBounds] using hρChart)
        hctrl.1 hctrl.2.1 hctrl.2.2).choose_spec.1
  have htgt (i : ι) : (z, xi i) ∈ e.target := by
    simpa only [z, xi, c] using
      IsNormalDiag.target_of_inv_dom (I := I) (X.obj k)
        hcomplete hconn x hq he hyCtrl.1 (hptCtrl i).1 (hdom i)
  have hyDecode : c.hom z = y := by
    with_unfolding_all
      exact c.restrictBall.right_inv hyCtrl.1
  have hptDecode (i : ι) : c.hom (xi i) = pts i := by
    with_unfolding_all
      exact c.restrictBall.right_inv (hptCtrl i).1
  have hreadDom (i : ι) :
      (c.hom z, c.hom (xi i)) ∈ B.chartReadDom c := by
    change (c.hom z, c.hom (xi i)) ∈ B.dom ∧
      c.hom z ∈ c.restrictBall.target
    rw [hyDecode, hptDecode]
    exact ⟨hdom i, hyCtrl.1⟩
  have hsum' : ∑ i : ι, mu i •
      (show TangentSpace I (c.hom z) from
        (B.inv (c.hom z, c.hom (xi i))).snd) = 0 := by
    rw [hyDecode]
    calc
      ∑ i : ι, mu i •
          (show TangentSpace I y from
            (B.inv (y, c.hom (xi i))).snd) =
          ∑ i : ι, mu i •
            (show TangentSpace I y from (B.inv (y, pts i)).snd) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hptDecode i]
      _ = 0 := hsum
  have hzero :
      chartCmEqnC (I := I) (X.obj k).metric
        (normal_enorm (I := I) (X.obj k)) x c B z (mu, xi) = 0 :=
    chartCmC_zero_of_sum (I := I) (X.obj k).metric
      (normal_enorm (I := I) (X.obj k)) x c B z mu xi
      hzBall hreadDom hsum'
  exact ⟨hyCtrl.1, hzBall, hxiBall, htgt, hreadDom, hzero⟩

theorem center_of_mass_satisfies_normal_coordinate_equation
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < 1)
    {ι : Type} [Fintype ι] (mu : ι → Real)
    (pts : ι → (X.obj k).M)
    (join : (X.obj k).M → (X.obj k).M → Real → (X.obj k).M)
    (p : (X.obj k).M) (r : Real)
    (hsum : ∑ i, mu i = 1) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    ∀ h : CenterInput (I := I) (X.obj k).metric mu pts join p r,
      0 < ρ →
      2 * ρ < (q : Real) →
      ρ ≤ (d.chart k x).radius →
      let y := centerOfMass (I := I) (X.obj k).metric mu pts join p r h
      (∀ i, max (riemannianEDist I x y)
          (riemannianEDist I x (pts i)) < ENNReal.ofReal (ρ / 2)) →
      let c := d.chart k x
      let B := IsNormalDiag.toBranch
        (I := I) (X.obj k) hcomplete hconn x hq he
      let z := c.inv y
      let xi : ι → E := fun i => c.inv (pts i)
      y ∈ c.restrictBall.target ∧
        HasCmSolC (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k)) x c B z (mu, xi) := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : (z : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  intro h hρ hρq hρChart
  dsimp only
  let y := centerOfMass (I := I) (X.obj k).metric mu pts join p r h
  intro hpairs
  let c := d.chart k x
  let B := IsNormalDiag.toBranch
    (I := I) (X.obj k) hcomplete hconn x hq he
  let z := c.inv y
  let xi : ι → E := fun i => c.inv (pts i)
  have hdata := d.center_of_mass_normal_coordinate_data
    k hcomplete hconn x hq he hf
    mu pts join p r h hρ hρq hρChart hpairs
  rcases hdata with ⟨hy, hz, hxi, htgt, hdom, hzero⟩
  have hsol := IsNormalDiag.cmC_sol_strict (I := I) (X.obj k)
    hcomplete hconn x hq he hf happrox heta z mu xi
    htgt h.μ_nonneg hsum ⟨hz, hxi, hdom, hzero⟩
  exact ⟨hy, hz, hxi, hdom, hzero, hsol⟩

end BoundedGeometryNormalChartData

end HCGCompactness
end DifferentialGeometry
