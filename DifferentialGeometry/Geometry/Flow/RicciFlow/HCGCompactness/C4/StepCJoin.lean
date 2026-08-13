import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCProducers
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

noncomputable local instance stepCJoinModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance stepCJoinModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance stepCJoinModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance stepCJoinModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem stepCJoinFixed (hd : InjRadiusDecayInput (I := I) X) {D : Real}
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
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ =>
          rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I)
        (M := (X.obj (L.φ n)).M)
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
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
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, B gamma a v ∈ V' gamma) :
    let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I)
      (M := (X.obj (L.φ n)).M)
    let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  exact NetLimitData.unifHatCageSelfComp hd P L pb r n rho hrho join radSeq center U V
    B Binf A Ainf hconn hX hcenter
    (fun gamma => hgp gamma (center gamma) (hcenter gamma))
    hrad hactive_mem hstrict hVopen hB hA hBcont hAcont hid hKU
    (fun gamma v hv =>
      hV'sub gamma (binfMemClosed (hB gamma) (hKU gamma hv) (hV'closed gamma)
        (Filter.Eventually.of_forall (hKV0 gamma v hv))))

theorem stepCJoinDataFixed (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (mu : (X.obj (L.φ n)).M -> Fin (pb.A r) -> Real)
    (hmu :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      centerAverage.WeightDataOn
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
        (fun gamma : Fin (pb.A r) =>
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) mu)
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ =>
          rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I)
        (M := (X.obj (L.φ n)).M)
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), mu x gamma ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill mu (ptsSeq a b)
              (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, B gamma a v ∈ V' gamma) :
    let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I)
      (M := (X.obj (L.φ n)).M)
    let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                mu
                (centerAverage.activeFill mu (ptsSeq a b)
                  (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric) (μ := mu)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hactive_mem a b y hy)
                  ((hmu.data hy).1.1) ((hmu.data hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  exact NetLimitData.unifHatCageData hd P L pb r n mu hmu join radSeq center U V
    B Binf A Ainf hconn hX hcenter
    (fun gamma => hgp gamma (center gamma) (hcenter gamma))
    hrad hactive_mem hstrict hVopen hB hA hBcont hAcont hid hKU
    (fun gamma v hv =>
      hV'sub gamma (binfMemClosed (hB gamma) (hKU gamma hv) (hV'closed gamma)
        (Filter.Eventually.of_forall (hKV0 gamma v hv))))

theorem stepCJoin (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (x y : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (U V Ua Va : Fin (pb.A r) -> Set E)
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
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (x gamma n))
    (hrad : forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
      xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b xx)
    (hU : forall gamma : Fin (pb.A r), IsOpen (U gamma))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hUa : forall gamma : Fin (pb.A r), IsOpen (Ua gamma))
    (hVa : forall gamma : Fin (pb.A r), IsOpen (Va gamma))
    (hUanorm : forall gamma : Fin (pb.A r),
      ∃ Z : Real, ∀ z ∈ Ua gamma, ‖z‖ ≤ Z)
    (hVanorm : forall gamma : Fin (pb.A r),
      ∃ Z : Real, ∀ z ∈ Va gamma, ‖z‖ ≤ Z)
    (hUmetric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      U gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (x gamma k)))
    (hVmetric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      V gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (y gamma k)))
    (hUametric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Ua gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (x gamma k)))
    (hVametric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Va gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (y gamma k)))
    (hUexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)))
    (hVexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      V gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (y gamma k)))
    (hUaexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Ua gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)))
    (hVaexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Va gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (y gamma k)))
    (hJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      ContDiffOn Real (⊤ : ℕ∞)
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k))
        (U gamma))
    (hJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      ContDiffOn Real (⊤ : ℕ∞)
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k))
        (V gamma))
    (hovlJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k) (U gamma))
    (hovlJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k) (V gamma))
    (hmapJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Set.MapsTo
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k))
        (U gamma) (Va gamma))
    (hmapJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Set.MapsTo
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k))
        (V gamma) (Ua gamma))
    (hLeft : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop, forall z, z ∈ U gamma ->
      normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k)
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k) z) = z)
    (hRight : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop, forall w, w ∈ V gamma ->
      normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k)
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k) w) = w)
    (hactive0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ =>
          rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I)
        (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
        xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma xx ≠ 0 ->
            dist xx (NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
              (fun gamma => x gamma n)
              (fun gamma a => normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a))
              (fun gamma b => normalTransition (I := I) (X.obj (L.φ b)) (y gamma b) (x gamma b))
              a b xx gamma) < radSeq a b xx)
    (hstrict0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
        xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
              (NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
                (fun gamma => x gamma n)
                (fun gamma a => normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a))
                (fun gamma b => normalTransition (I := I) (X.obj (L.φ b)) (y gamma b) (x gamma b))
                a b)
              (fun yy : (X.obj (L.φ n)).M => yy) xx)
            join xx (radSeq a b xx))
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (x gamma n)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (x gamma n)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a) v ∈ V'
          gamma) :
    exists phi : Nat -> Nat, StrictMono phi /\
      (let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
       letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
       letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
       letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
       letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
       letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
       letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
       letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
       letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
         Manifold.metrizableSpace I (X.obj (L.φ n)).M
       letI : T3Space (X.obj (L.φ n)).M := inferInstance
       letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
         ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
       letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
         ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ =>
           rfl⟩
       letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I)
         (M := (X.obj (L.φ n)).M)
       let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
         (fun gamma => x gamma n)
         (fun gamma a => normalTransition (I := I) (X.obj (L.φ (phi a))) (x gamma (phi a))
           (y gamma (phi a)))
         (fun gamma b => normalTransition (I := I) (X.obj (L.φ (phi b))) (y gamma (phi b))
           (x gamma (phi b)))
       forall eps : Real, eps > 0 -> exists N : Nat,
         forall a : Nat, a >= N -> forall b : Nat, b >= N ->
           forall xx : (X.obj (L.φ n)).M,
             xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
               dist xx
                 (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                   (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                   (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                   (centerAverage.activeFill
                     (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                     (ptsSeq a b) (fun yy : (X.obj (L.φ n)).M => yy))
                   join (fun yy : (X.obj (L.φ n)).M => yy)
                   (fun xx => radSeq (phi a) (phi b) xx)
                   (fun yy : (X.obj (L.φ n)).M => yy)
                   (fun yy hy => centerAverage.inputOfFillSelf (I := I)
                     (g := (X.obj (L.φ n)).metric)
                     (μ := fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                     (pts := ptsSeq a b) (join := join)
                     (r := fun xx => radSeq (phi a) (phi b) xx)
                       (qstar := fun yy : (X.obj (L.φ n)).M => yy)
                     yy hcomplete (hrad (phi a) (phi b) yy hy) (hactive0 (phi a) (phi b) yy hy)
                     ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                       (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                       (rho := rho) (hrho := hrho) a b hy).1.1)
                     ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                       (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                       (rho := rho) (hrho := hrho) a b hy).1.2.1)
                     (hstrict0 (phi a) (phi b) yy hy)) xx) < eps) := by
  classical
  have htail (gamma : Fin (pb.A r)) : ∀ᶠ k in atTop,
      NormalTransAt (I := I)
        (NormalCoordMetricBoundInput.subseq (I := I) metricInput L.φ)
        x y U V Ua Va gamma k := by
    filter_upwards
      [hUmetric gamma, hVmetric gamma, hUametric gamma, hVametric gamma,
        hUexp gamma, hVexp gamma, hUaexp gamma, hVaexp gamma,
        hJ gamma, hJbar gamma, hovlJ gamma, hovlJbar gamma,
        hmapJ gamma, hmapJbar gamma, hLeft gamma, hRight gamma]
      with k hkUM hkVM hkUaM hkVaM hkUE hkVE hkUaE hkVaE
        hkJ hkJbar hkOvl hkOvlbar hkMap hkMapbar hkLeft hkRight
    exact
      { Umetric := hkUM
        Vmetric := hkVM
        Uametric := hkUaM
        Vametric := hkVaM
        Uexp := hkUE
        Vexp := hkVE
        Uaexp := hkUaE
        Vaexp := hkVaE
        J := hkJ
        Jbar := hkJbar
        ovlJ := hkOvl
        ovlJbar := hkOvlbar
        mapJ := hkMap
        mapJbar := hkMapbar
        left := hkLeft
        right := hkRight }
  obtain ⟨phi, hphi, Jinf, Jbarinf, hspec⟩ :=
    existsTransTail (I := I) (X := X.subseq L.φ)
      (NormalCoordMetricBoundInput.subseq (I := I) metricInput L.φ)
      x y U V Ua Va hU hVopen hUa hVa hUanorm hVanorm htail
  refine ⟨phi, hphi, ?_⟩
  exact stepCJoinFixed hd P L pb r n rho hrho join
    (fun a b => radSeq (phi a) (phi b))
    (fun gamma => x gamma n) U V
    (fun gamma a => normalTransition (I := I) (X.obj (L.φ (phi a))) (x gamma (phi a))
      (y gamma (phi a)))
    Jinf
    (fun gamma b => normalTransition (I := I) (X.obj (L.φ (phi b))) (y gamma (phi b))
      (x gamma (phi b)))
    Jbarinf
    hconn hX hcenter hgp
    (fun a b => hrad (phi a) (phi b))
    (fun a b => hactive0 (phi a) (phi b))
    (fun a b => hstrict0 (phi a) (phi b))
    hVopen
    (fun gamma => by
      simpa only [PointedRiemannianSeq.subseq] using (hspec gamma).2.2.2.2.1)
    (fun gamma => by
      simpa only [PointedRiemannianSeq.subseq] using (hspec gamma).2.2.2.2.2.1)
    (fun gamma => (hspec gamma).2.2.1)
    (fun gamma => (hspec gamma).2.2.2.1)
    (fun gamma => (hspec gamma).2.2.2.2.2.2.1)
    hKU V' hV'closed hV'sub
    (fun gamma v hv a => hKV0 gamma v hv (phi a))

end HCGCompactness
end DifferentialGeometry
