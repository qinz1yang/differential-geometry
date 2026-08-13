import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.HatChartConvergence
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

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

noncomputable def hatSourceBall (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (r : Real) (n : Nat) :
    Set (X.obj (L.φ n)).M :=
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  Metric.closedBall (X.obj (L.φ n)).basepoint r

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem hatSourceBall_subseq
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (r : Real) (n : Nat) {ψ : Nat -> Nat} (hψ : StrictMono ψ) :
    NetLimitData.hatSourceBall (I := I) (X := X) hd P (L.subseq hψ) r n =
      NetLimitData.hatSourceBall (I := I) (X := X) hd P L r (ψ n) := rfl

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatSource_nhds
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    {R s : Real} (n : Nat) (hRs : R < s)
    {x : (X.obj (L.φ n)).M}
    (hx : x ∈ hatSourceBall (I := I) (X := X) hd P L R n) :
    letI : TopologicalSpace (X.obj (L.φ n)).M :=
      (X.obj (L.φ n)).topology
    hatSourceBall (I := I) (X := X) hd P L s n ∈ nhds x := by
  let Y := X.obj (L.φ n)
  letI : TopologicalSpace Y.M := Y.topology
  have hopen :
      @IsOpen Y.M Y.topology
        (letI : MetricSpace Y.M := (P (L.φ n)).ms
         Metric.ball Y.basepoint s) := by
    have hb :
        @IsOpen Y.M
          (P (L.φ n)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (letI : MetricSpace Y.M := (P (L.φ n)).ms
           Metric.ball Y.basepoint s) := by
      letI : MetricSpace Y.M := (P (L.φ n)).ms
      exact Metric.isOpen_ball
    rw [ProperMetricOn.top_eq Y (P (L.φ n))] at hb
    exact hb
  have hxopen :
      x ∈ (letI : MetricSpace Y.M := (P (L.φ n)).ms
        Metric.ball Y.basepoint s) := by
    letI : MetricSpace Y.M := (P (L.φ n)).ms
    exact Metric.closedBall_subset_ball hRs
      (by simpa only [hatSourceBall] using hx)
  refine mem_of_superset (hopen.mem_nhds hxopen) ?_
  intro y hy
  letI : MetricSpace Y.M := (P (L.φ n)).ms
  simpa only [hatSourceBall] using (Metric.ball_subset_closedBall hy)


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatSourceCompact
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (r : Real) (n : Nat) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    IsCompact (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n) := by
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have htop := ProperMetricOn.top_eq (X.obj (L.φ n)) (P (L.φ n))
  have hcompact :
      @IsCompact (X.obj (L.φ n)).M
        (P (L.φ n)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n) := by
    simpa [NetLimitData.hatSourceBall] using
      (isCompact_closedBall (X.obj (L.φ n)).basepoint r)
  rw [← htop]
  exact hcompact

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem sourceComplete
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (n : Nat) (hX : SeqMetricComplete (I := I) X)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M) :
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
    CompleteSpace (X.obj (L.φ n)).M := by
  have h := MetricComplete.complete (I := I) (X.obj (L.φ n)) (hX.complete (L.φ n))
  simpa using h


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatBallInCompact
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (gamma : Fin (pb.A r)) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    exists K : Set (X.obj (L.φ k)).M, IsCompact K ∧
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := k) (γ := gamma) :
        Set (X.obj (L.φ k)).M) ⊆ K := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  have htop := ProperMetricOn.top_eq (X.obj (L.φ k)) (P (L.φ k))
  cases hcenter : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      refine ⟨∅, isCompact_empty, ?_⟩
      intro x hx
      simp [NetLimitData.hatBall, hcenter] at hx
  | some c =>
      refine ⟨Metric.closedBall c (4 * L.lamInf (gamma : Nat)), ?_, ?_⟩
      · have hcompact :
            @IsCompact (X.obj (L.φ k)).M
              (P (L.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
              (Metric.closedBall c (4 * L.lamInf (gamma : Nat))) := by
          simpa using (isCompact_closedBall c (4 * L.lamInf (gamma : Nat)))
        rw [← htop]
        exact hcompact
      · intro x hx
        have hdist : dist x c < 4 * L.lamInf (gamma : Nat) := by
          simpa [NetLimitData.hatBall, hcenter, Metric.mem_ball] using hx
        simpa [Metric.mem_closedBall] using le_of_lt hdist

noncomputable def hatSourceCage (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) (gamma : Fin (pb.A r)) :
    Set (X.obj (L.φ n)).M :=
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  closure
    (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
      (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
        (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
        Set (X.obj (L.φ n)).M))

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem hatSourceCage_subseq
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) (gamma : Fin (pb.A r))
    {ψ : Nat -> Nat} (hψ : StrictMono ψ) :
    NetLimitData.hatSourceCage (I := I) (X := X) hd P (L.subseq hψ) pb r n gamma =
      NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r (ψ n) gamma := by
  simp [hatSourceCage]
  rfl


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatCageData
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) (gamma : Fin (pb.A r)) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    IsCompact (NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma) ∧
      (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)) ⊆
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let S : Set (X.obj (L.φ n)).M :=
    NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n
  let H : Set (X.obj (L.φ n)).M :=
    NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
      (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma)
  have hScompact : IsCompact S := by
    simpa [S] using
      NetLimitData.hatSourceCompact (I := I) (X := X) hd P L r n
  have hclosureS : closure (S ∩ H) ⊆ S := by
    exact closure_minimal inter_subset_left hScompact.isClosed
  have hcompact : IsCompact (closure (S ∩ H)) :=
    hScompact.of_isClosed_subset isClosed_closure hclosureS
  refine ⟨?_, ?_⟩
  · simpa [NetLimitData.hatSourceCage, S, H] using hcompact
  · simpa [NetLimitData.hatSourceCage, S, H] using
      (subset_closure : S ∩ H ⊆ closure (S ∩ H))


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatCageCompact
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    forall gamma : Fin (pb.A r),
      IsCompact (NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  intro gamma
  exact (NetLimitData.hatCageData (I := I) (X := X) hd P L pb r n gamma).1

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatCageSub
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    forall gamma : Fin (pb.A r),
      (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)) ⊆
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  intro gamma
  exact (NetLimitData.hatCageData (I := I) (X := X) hd P L pb r n gamma).2

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hatCageInClosed
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) (gamma : Fin (pb.A r))
    {c : (X.obj (L.φ n)).M}
    (hc : seqCenter hd D P (L.φ n) (gamma : Nat) = some c) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      Metric.closedBall c (4 * L.lamInf (gamma : Nat)) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  have htop := ProperMetricOn.top_eq (X.obj (L.φ n)) (P (L.φ n))
  have hclosed :
      @IsClosed (X.obj (L.φ n)).M (X.obj (L.φ n)).topology
        (Metric.closedBall c (4 * L.lamInf (gamma : Nat))) := by
    have hclosed_metric :
        @IsClosed (X.obj (L.φ n)).M
          (P (L.φ n)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (Metric.closedBall c (4 * L.lamInf (gamma : Nat))) := by
      simpa using
        (Metric.isClosed_closedBall :
          @IsClosed (X.obj (L.φ n)).M
            (P (L.φ n)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
            (Metric.closedBall c (4 * L.lamInf (gamma : Nat))))
    rw [← htop]
    exact hclosed_metric
  have hsub :
      (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)) ⊆
        Metric.closedBall c (4 * L.lamInf (gamma : Nat)) := by
    intro x hx
    have hdist : dist x c < 4 * L.lamInf (gamma : Nat) := by
      simpa [NetLimitData.hatBall, hc, Metric.mem_ball] using hx.2
    simpa [Metric.mem_closedBall] using le_of_lt hdist
  simpa [NetLimitData.hatSourceCage] using closure_minimal hsub hclosed

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank Real E)] in
theorem hatCageSrcOfBall
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hball :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      Metric.closedBall (center gamma) (4 * L.lamInf (gamma : Nat)) ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
        (center gamma)).source := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  exact
    (NetLimitData.hatCageInClosed (I := I) (X := X) hd P L pb r n gamma hcenter).trans
      hball

omit [Module.Finite ℝ E] in
theorem hatCageSrcOfRad
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) <
        expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma)) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
        (center gamma)).source := by
  exact
    NetLimitData.hatCageSrcOfBall (I := I) (X := X) hd P L pb r n center gamma
      hcenter
      (properBallSrcOfRad (I := I) (Y := X.obj (L.φ n)) (P := P (L.φ n)) hR)

omit [Module.Finite ℝ E] in
theorem hatCageSrcCases
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall c : (X.obj (L.φ n)).M,
        seqCenter hd D P (L.φ n) (gamma : Nat) = some c ->
          c = center gamma ∧
            4 * L.lamInf (gamma : Nat) <
              expRadiusGp (I := I) (X.obj (L.φ n)).metric c) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    forall gamma : Fin (pb.A r),
      NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source := by
  intro gamma
  cases hc : seqCenter hd D P (L.φ n) (gamma : Nat) with
  | none =>
      simp [NetLimitData.hatSourceCage, NetLimitData.hatBall, hc]
  | some c =>
      rcases hR gamma c hc with ⟨rfl, hrad⟩
      exact NetLimitData.hatCageSrcOfRad (I := I) (X := X) hd P L pb r n center
        gamma hc hrad

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank Real E)] in
theorem hatSuppCageData
    [FiniteDimensional Real E]
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (_pb : hd.PackingBound D) (_r : Real) (n : Nat)
    {s : Set (X.obj (L.φ n)).M} {ι : Type*}
    (mu : (X.obj (L.φ n)).M -> ι -> Real)
    (center : ι -> (X.obj (L.φ n)).M)
    (sourceCage : ι -> Set (X.obj (L.φ n)).M)
    (U V' : ι -> Set E)
    (Binf : ι -> E -> E)
    (hCageCompact :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : ι, IsCompact (sourceCage gamma))
    (hSuppCage :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : ι, forall x : (X.obj (L.φ n)).M,
        x ∈ s ->
        mu x gamma ≠ 0 -> x ∈ sourceCage gamma)
    (hsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι,
        sourceCage gamma ⊆
          (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
            (center gamma)).source)
    (hBcont : forall gamma : ι, ContinuousOn (Binf gamma) (U gamma))
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι,
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            sourceCage gamma ⊆
          U gamma)
    (hV'closed : forall gamma : ι, IsClosed (V' gamma))
    (hSuppV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι, forall x : (X.obj (L.φ n)).M,
        x ∈ s ->
        mu x gamma ≠ 0 ->
          Binf gamma
              ((NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
                (center gamma)) x) ∈ V' gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    ∃ sourceK : ι -> Set (X.obj (L.φ n)).M,
      (forall gamma : ι, IsCompact (sourceK gamma)) ∧
      (forall gamma : ι, forall x : (X.obj (L.φ n)).M,
        x ∈ s ->
        mu x gamma ≠ 0 -> x ∈ sourceK gamma) ∧
      (forall gamma : ι, sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source) ∧
      (forall gamma : ι,
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma ⊆ U gamma) ∧
      (forall gamma : ι, forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma -> Binf gamma v ∈ V' gamma) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  let sourceBall : Set (X.obj (L.φ n)).M := s
  let chart : ι -> (X.obj (L.φ n)).M -> E := fun gamma =>
    NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
      (center gamma)
  let support : ι -> Set (X.obj (L.φ n)).M := fun gamma =>
    {x | x ∈ sourceBall ∧ mu x gamma ≠ 0}
  let sourceK : ι -> Set (X.obj (L.φ n)).M := fun gamma =>
    closure (support gamma)
  have hKsub (gamma : ι) : sourceK gamma ⊆ sourceCage gamma := by
    apply closure_minimal
    · intro x hx
      exact hSuppCage gamma x hx.1 hx.2
    · exact (hCageCompact gamma).isClosed
  refine ⟨sourceK, ?_, ?_, ?_, ?_, ?_⟩
  · intro gamma
    exact (hCageCompact gamma).of_isClosed_subset isClosed_closure (hKsub gamma)
  · intro gamma x hx hmu
    exact subset_closure ⟨hx, hmu⟩
  · intro gamma x hx
    exact hsrc gamma (hKsub gamma hx)
  · intro gamma v hv
    rcases hv with ⟨x, hx, rfl⟩
    exact hKU gamma ⟨x, hKsub gamma hx, rfl⟩
  · intro gamma v hv
    rcases hv with ⟨x, hx, rfl⟩
    have hchart : ContinuousOn (chart gamma) (sourceCage gamma) :=
      (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
        (center gamma)).contMDiffOn_toFun.continuousOn.mono (hsrc gamma)
    have hcomp : ContinuousOn (fun y => Binf gamma (chart gamma y))
        (sourceCage gamma) :=
      (hBcont gamma).comp' hchart (by
        intro y hy
        exact hKU gamma ⟨y, hy, rfl⟩)
    have hclosed : IsClosed
        (sourceCage gamma ∩
          (fun y => Binf gamma (chart gamma y)) ⁻¹' V' gamma) :=
      hcomp.preimage_isClosed_of_isClosed (hCageCompact gamma).isClosed
        (hV'closed gamma)
    have hsupp : support gamma ⊆
        sourceCage gamma ∩
          (fun y => Binf gamma (chart gamma y)) ⁻¹' V' gamma := by
      intro y hy
      exact ⟨hSuppCage gamma y hy.1 hy.2, hSuppV gamma y hy.1 hy.2⟩
    exact (closure_minimal hsupp hclosed hx).2

end NetLimitData

end HCGCompactness
end DifferentialGeometry
