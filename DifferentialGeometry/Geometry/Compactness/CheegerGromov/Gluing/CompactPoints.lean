import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.SourceCage


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
[InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

namespace NetLimitData

omit [FiniteDimensional ℝ E] in
omit [CompleteSpace E] in
theorem hatPtsOfCompact
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (ptsSeq :
      Nat -> Nat -> (X.obj (L.φ n)).M -> Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hconv :
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
      forall gamma : Fin (pb.A r), forall K : Set (X.obj (L.φ n)).M,
        IsCompact K ->
          (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
            (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M)) ⊆ K ->
          forall eps : Real, eps > 0 -> exists N : Nat,
            forall a : Nat, a >= N -> forall b : Nat, b >= N ->
              forall x : (X.obj (L.φ n)).M, x ∈ K ->
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
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x (ptsSeq a b x gamma) < eps := by
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
  intro gamma eps heps
  obtain ⟨K, hK, hhatK⟩ :=
    NetLimitData.hatBallInCompact (I := I) (X := X) hd P L pb r n gamma
  have hsub :
      (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)) ⊆ K := by
    intro x hx
    exact hhatK hx.2
  obtain ⟨N, hN⟩ := hconv gamma K hK hsub eps heps
  refine ⟨N, fun a ha b hb x hxsrc hxhat => ?_⟩
  exact hN a ha b hb x (hsub ⟨hxsrc, hxhat⟩)

omit [FiniteDimensional ℝ E] in
theorem hatChartPts
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (coordK : Fin (pb.A r) -> Set E)
    (F : Fin (pb.A r) -> Nat -> Nat -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      ∀ gamma : Fin (pb.A r), IsCompact (coordK gamma))
    (hKtarget :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), coordK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).target)
    (hsource :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), ∀ x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        x ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hcoord :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), ∀ x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) x ∈ coordK gamma)
    (hclose : ∀ gamma : Fin (pb.A r), ∀ δ : Real, δ > 0 -> ∃ N : Nat,
      ∀ a : Nat, a >= N -> ∀ b : Nat, b >= N -> ∀ v : E, v ∈ coordK gamma ->
        dist (F gamma a b v) v < δ) :
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
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (F gamma a b ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x))) < eps := by
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
  intro gamma eps heps
  let S : Set (X.obj (L.φ n)).M :=
    NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M)
  have hSsource : ∀ x : (X.obj (L.φ n)).M, x ∈ S ->
      x ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
        (center gamma)).source := by
    intro x hx
    exact hsource gamma x hx.1 hx.2
  have hScoord : ∀ x : (X.obj (L.φ n)).M, x ∈ S ->
      (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
        (center gamma)) x ∈ coordK gamma := by
    intro x hx
    exact hcoord gamma x hx.1 hx.2
  obtain ⟨N, hN⟩ :=
    chartPtsConv (I := I) (g := (X.obj (L.φ n)).metric)
      (p := center gamma) (S := S) (K := coordK gamma)
      (hK gamma) (hKtarget gamma) hSsource hScoord (F gamma)
      (hclose gamma) eps heps
  refine ⟨N, fun a ha b hb x hxsrc hxhat => ?_⟩
  exact hN a ha b hb x ⟨hxsrc, hxhat⟩

omit [FiniteDimensional ℝ E] in
theorem hatChartPtsSrcK
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M)
    (F : Fin (pb.A r) -> Nat -> Nat -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hKsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ∀ gamma : Fin (pb.A r), IsCompact (sourceK gamma))
    (hSsub :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ∀ gamma : Fin (pb.A r),
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) ⊆ sourceK gamma)
    (hsrcK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hclose :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), ∀ δ : Real, δ > 0 -> ∃ N : Nat,
        ∀ a : Nat, a >= N -> ∀ b : Nat, b >= N -> ∀ v : E,
          v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
            (center gamma)) '' sourceK gamma ->
            dist (F gamma a b v) v < δ) :
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
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (F gamma a b ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x))) < eps := by
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
  intro gamma eps heps
  let S : Set (X.obj (L.φ n)).M :=
    NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M)
  obtain ⟨N, hN⟩ :=
    chartPtsSrcK (I := I) (g := (X.obj (L.φ n)).metric)
      (p := center gamma) (S := S) (Ksrc := sourceK gamma)
      (hKsrc gamma) (hSsub gamma) (hsrcK gamma) (F gamma)
      (hclose gamma) eps heps
  refine ⟨N, fun a ha b hb x hxsrc hxhat => ?_⟩
  exact hN a ha b hb x ⟨hxsrc, hxhat⟩

end NetLimitData

end HCGCompactness
end DifferentialGeometry
