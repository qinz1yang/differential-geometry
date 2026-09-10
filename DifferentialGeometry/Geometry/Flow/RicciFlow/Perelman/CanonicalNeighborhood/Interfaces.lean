import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.SmoothCheegerGromovLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def PointedFlowCurvatureOperatorLowerBound
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (t : Real) (K : Real → Real) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  ∀ x : F.M, ∀ (n : Nat) (c : Fin n → Real) (v w : Fin n → TangentSpace I x),
    0 ≤ ∑ i, ∑ j, c i * c j *
      (F.S.base.rm04 t x (vec4 (I := I) (v i) (w i) (w j) (v j)) +
        K (F.S.scalar t x) *
          ((F.S.base.metric t).inner x (v i) (v j) *
              (F.S.base.metric t).inner x (w i) (w j) -
            (F.S.base.metric t).inner x (v i) (w j) *
              (F.S.base.metric t).inner x (w i) (v j)))

def PointedFlowRmNormLeScalar
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (C : Real) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  ∀ t ∈ D.carrier, ∀ x : F.M,
    Real.sqrt (F.rmNormSq (I := I) t x) ≤ C * F.S.scalar t x

def PointedFlowSpatiallyKappaNoncollapsed
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (kappa : Real) (scales : Set Real) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I 1 F.M :=
    IsManifold.of_le (I := I) (M := F.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  ∀ (time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D)
    (B : Perelman.FlowMetricBall (I := I) (M := F.M) F.S time),
    B.radius ∈ scales →
    (∀ x ∈ B.set, B.radius ^ 4 *
        Perelman.FlowMetricBall.rmNormSq (I := I) F.S (time : Real) x ≤ 1) →
      B.IsKappaNoncollapsed kappa

def SourceBallCapture
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) subseq) : Prop :=
  ∀ r : Real, 0 < r → ∀ᶠ k : Nat in Filter.atTop,
    letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
    letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
      change IsManifold I ∞ (X.term (subseq k)).M
      infer_instance
    letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
    letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    {y : (X.term (subseq k)).M |
        DifferentialGeometry.riemannianEDistOf (I := I)
          ((X.term (subseq k)).S.base.metric 0)
          (X.term (subseq k)).basepoint y < ENNReal.ofReal r} ⊆
      Set.range (Φ.map (I := I) k)

def BlowUpLimitNonnegativeCurvature (I : ModelWithCorners Real E H) : Prop :=
  ∀ (Phi : Real → Real) (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (subseq : Nat → Nat) (Q : Nat → Real),
    (∀ k : Nat, 0 < Q k) →
    Filter.Tendsto Q Filter.atTop Filter.atTop →
    (∀ k : Nat, ∀ t ∈ X.D.carrier,
      PointedFlowCurvatureOperatorLowerBound (I := I) (X.term (subseq k)) t
        (fun s => (Q k)⁻¹ * Phi (Q k * s))) →
    Nonempty (SmoothCGHConverges (I := I) X L subseq) →
    ∀ t ∈ X.D.carrier,
      PointedFlowCurvatureOperatorLowerBound (I := I) L t (fun _ => 0)

def NoncollapsePassesToLimit (I : ModelWithCorners Real E H) : Prop :=
  ∀ (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (subseq : Nat → Nat)
    (Q : Nat → Real) (kappa rho : Real),
    0 < kappa → 0 < rho →
    (∀ k : Nat, 0 < Q k) →
    Filter.Tendsto Q Filter.atTop Filter.atTop →
    (∀ k : Nat, PointedFlowSpatiallyKappaNoncollapsed (I := I) (X.term (subseq k)) kappa
      (Set.Ioc 0 (Real.sqrt (Q k) * rho))) →
    ∀ conv : SmoothCGHConverges (I := I) X L subseq,
      SourceBallCapture (I := I) conv.spatial.maps →
      PointedFlowSpatiallyKappaNoncollapsed (I := I) L kappa Set.univ

def RmNormBoundedByScalarCurvature (I : ModelWithCorners Real E H) : Prop :=
  ∃ C : Real, 0 ≤ C ∧
    ∀ (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
      (F : PointedFlowData.{u, uE, uH} (I := I) D),
      (∀ t ∈ D.carrier,
        PointedFlowCurvatureOperatorLowerBound (I := I) F t (fun _ => 0)) →
      PointedFlowRmNormLeScalar (I := I) F C

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
