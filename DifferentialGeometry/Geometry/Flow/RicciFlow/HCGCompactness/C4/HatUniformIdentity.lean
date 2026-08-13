import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.HatPartitionData
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

namespace NetLimitData

omit [Module.Finite ℝ E] in
omit [CompleteSpace E] in
theorem unifHatIdOn
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (ptsSeq :
      Nat -> Nat -> (X.obj (L.φ n)).M -> Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (pSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hcomplete :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace (X.obj (L.φ n)).M :=
        EMetricSpace.ofRiemannianMetric I (X.obj (L.φ n)).M
      CompleteSpace (X.obj (L.φ n)).M)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hqstar :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          dist (pSeq a b x) x < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist (pSeq a b x) (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join (pSeq a b x) (radSeq a b x))
    (hpts :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
        forall a : Nat, a >= N -> forall b : Nat, b >= N ->
          forall x : (X.obj (L.φ n)).M,
            x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
              x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
                (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
                Set (X.obj (L.φ n)).M) ->
                dist x (ptsSeq a b x gamma) < eps) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M =>
                  fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (pSeq a b) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFill (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join) (p := pSeq a b)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hqstar a b y hy)
                  (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  exact centerAverage.unifTwoIdDataOn (I := I)
    (g := (X.obj (L.φ n)).metric) (join := join)
    (s := NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
    (USeq := fun _ _ gamma =>
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M))
    (μSeq := fun _ _ y gamma => rho gamma y) (ptsSeq := ptsSeq)
    (pSeq := pSeq) (rSeq := radSeq) hcomplete hrad hqstar hactive_mem
    (fun a b y hy =>
      NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (n := n) (rho := rho)
        (hrho := hrho) a b hy)
    hstrict hpts

omit [Module.Finite ℝ E] in
omit [CompleteSpace E] in
theorem unifHatIdSelfOn
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (ptsSeq :
      Nat -> Nat -> (X.obj (L.φ n)).M -> Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hcomplete :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace (X.obj (L.φ n)).M :=
        EMetricSpace.ofRiemannianMetric I (X.obj (L.φ n)).M
      CompleteSpace (X.obj (L.φ n)).M)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hpts :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner,
          (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
        forall a : Nat, a >= N -> forall b : Nat, b >= N ->
          forall x : (X.obj (L.φ n)).M,
            x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
              x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
                (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
                Set (X.obj (L.φ n)).M) ->
                dist x (ptsSeq a b x gamma) < eps) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M =>
                  fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M =>
                    fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy)
                  (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  exact centerAverage.unifTwoIdDataSelf (I := I)
    (g := (X.obj (L.φ n)).metric) (join := join)
    (s := NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
    (USeq := fun _ _ gamma =>
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M))
    (μSeq := fun _ _ y gamma => rho gamma y) (ptsSeq := ptsSeq)
    (rSeq := radSeq) hcomplete hrad hactive_mem
    (fun a b y hy =>
      NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (n := n) (rho := rho)
        (hrho := hrho) a b hy)
    hstrict hpts

end NetLimitData

end HCGCompactness
end DifferentialGeometry
