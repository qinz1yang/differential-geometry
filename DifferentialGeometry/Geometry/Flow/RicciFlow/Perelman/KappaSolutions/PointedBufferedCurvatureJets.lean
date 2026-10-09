import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BufferedMixedCurvature
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance pointedBufferedTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance pointedBufferedCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance pointedBufferedSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance pointedBufferedC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance pointedBufferedT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance pointedBufferedSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance pointedBufferedTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

private local instance pointedBufferedMetricTopology
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace P.M := P.topology
private local instance pointedBufferedMetricCharted
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H P.M := P.charted
private local instance pointedBufferedMetricSmooth
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ P.M := P.smooth


theorem exists_pointed_buffered_mixed_curvature_bounds
    (hdim : Module.finrank ℝ E = 3)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (hnormalized : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (C : MetricConvergenceData (I := I) (Phi.atTime (L := L) 0))
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
      (I := I) (Phi.atTime (L := L) 0) i)
    (hcomplete : MetricComplete (I := I) (L.atTime (I := I) 0))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ B : ℕ → ℕ → ℝ, (∀ p q, 0 < B p q) ∧ ∃ N : ℕ, ∀ i ≥ N,
      riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint A ⊆ Phi.source i ∧
      ∀ x ∈ riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint A,
        riemannianEDistOf (I := I) ((X.term (phi i)).S.base.metric 0)
          (X.term (phi i)).basepoint (Phi.map i x) ≤ ENNReal.ofReal (2 * A) ∧
        ∀ p q : ℕ, ∀ t : ℝ, t ≤ 0 →
          DifferentiableWithinAt ℝ
            (fun s => mixedCurvatureTensor (X.term (phi i)).S p q s (Phi.map i x)) (Iic 0) t ∧
          mixedCurvatureNorm (X.term (phi i)).S p q t (Phi.map i x) ≤ B p q := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  choose B hB hbound using
    fun p q : ℕ => exists_normalized_klim_mixed_jet_bound (I := I)
      hdim kappa (2 * A) (by positivity) p q
  have hmetricComplete : RiemannianMetricComplete (I := I) (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (I := I) (L.atTime (I := I) 0) hcomplete⟩
  let K := riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint (A + 1)
  have hK : IsCompact K := hmetricComplete.closedEBall_isCompact L.basepoint (A + 1)
  have href (i : ℕ) : (C.domain i).referenceMetric = (C.domain i).limitMetric := by
    rw [hcanonical i]
    rfl
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control C href K hK 1 zero_lt_one
  refine ⟨B, hB, N, fun i hi => ?_⟩
  have hin : riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint A ⊆ K :=
    fun x hx => hx.trans (ENNReal.ofReal_le_ofReal (by linarith))
  refine ⟨fun x hx => (hN i hi).1 (hin hx), fun x hx => ?_⟩
  have hupper : ∀ y ∈ K, ∀ v : TangentSpace I y,
      ((X.term (phi i)).S.base.metric 0).inner (Phi.map i y)
          (mfderiv I I (Phi.map i) y v) (mfderiv I I (Phi.map i) y v) ≤
        (2 : ℝ) ^ 2 * (L.S.base.metric 0).inner y v v := by
    intro y hy v
    have herr := (abs_le.mp ((hN i hi).2 (y : L.M) hy v)).2
    change ((X.term (phi i)).S.base.metric 0).inner (Phi.map i (y : L.M))
      (mfderiv I I (Phi.map i) (y : L.M) v) (mfderiv I I (Phi.map i) (y : L.M) v) -
        (L.S.base.metric 0).inner y v v ≤ 1 * (L.S.base.metric 0).inner y v v at herr
    have hnonneg : 0 ≤ (L.S.base.metric 0).inner y v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact ((L.S.base.metric 0).pos y v hv).le
    nlinarith
  have hxR : riemannianEDistOf (I := I) (L.S.base.metric 0) L.basepoint x <
      ENNReal.ofReal (A + 1) :=
    hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < A + 1)).mpr (by linarith))
  have hdist := edistOf_map_le_of_metric_upper_on_ball
    (L.S.base.metric 0) ((X.term (phi i)).S.base.metric 0)
    ((Phi.atTime (L := L) 0).partialDiffeomorph i) L.basepoint x
    (by linarith : 0 < A + 1) (by norm_num : (0 : ℝ) < 2) (hN i hi).1 hupper hxR
  change riemannianEDistOf (I := I) ((X.term (phi i)).S.base.metric 0)
    (Phi.map i L.basepoint) (Phi.map i x) ≤
      ENNReal.ofReal 2 * riemannianEDistOf (I := I) (L.S.base.metric 0) L.basepoint x at hdist
  have hbase : Phi.map i L.basepoint = (X.term (phi i)).basepoint := Phi.basepoint_map i
  have hdistBase : riemannianEDistOf (I := I) ((X.term (phi i)).S.base.metric 0)
      (X.term (phi i)).basepoint (Phi.map i x) ≤
        ENNReal.ofReal 2 * riemannianEDistOf (I := I) (L.S.base.metric 0) L.basepoint x :=
    (congrArg (fun y => riemannianEDistOf (I := I) ((X.term (phi i)).S.base.metric 0)
      y (Phi.map i x)) hbase).symm.le.trans hdist
  have hball : riemannianEDistOf (I := I) ((X.term (phi i)).S.base.metric 0)
      (X.term (phi i)).basepoint (Phi.map i x) ≤ ENNReal.ofReal (2 * A) := by
    calc
      _ ≤ ENNReal.ofReal 2 * riemannianEDistOf (I := I) (L.S.base.metric 0)
          L.basepoint x := hdistBase
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal A := mul_le_mul' le_rfl hx
      _ = ENNReal.ofReal (2 * A) := (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
  exact ⟨hball, fun p q t ht => hbound p q X.D (X.term (phi i))
    (hsource (phi i)) (hnormalized (phi i)) t ht (Phi.map i x) hball⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
