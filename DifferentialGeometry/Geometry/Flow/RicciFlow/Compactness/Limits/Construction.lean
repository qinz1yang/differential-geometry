import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry

namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

def flowOfMetric
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (g :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (hsol :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      letI : T2Space P.M := P.t2
      letI : IsManifold I 1 P.M :=
        IsManifold.of_le (I := I) (M := P.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
        change IsManifold I ∞ P.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := g } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := P.M) D)) :
    PointedFlowData.{u, uE, uH} (I := I) D where
  M := P.M
  topology := P.topology
  charted := P.charted
  smooth := P.smooth
  sigmaCompact := P.sigmaCompact
  t2 := P.t2
  t2TangentBundle := P.t2TangentBundle
  basepoint := P.basepoint
  S :=
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
      change IsManifold I ∞ P.M
      infer_instance
    ({ base := { metric := g } } :
      DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := P.M) D)
  isSolution := hsol

theorem flowOfMetric_metric
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (g :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (hsol :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      letI : T2Space P.M := P.t2
      letI : IsManifold I 1 P.M :=
        IsManifold.of_le (I := I) (M := P.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
        change IsManifold I ∞ P.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := g } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := P.M) D)) :
    letI : TopologicalSpace (flowOfMetric (I := I) D P g hsol).M :=
      (flowOfMetric (I := I) D P g hsol).topology
    letI : ChartedSpace H (flowOfMetric (I := I) D P g hsol).M :=
      (flowOfMetric (I := I) D P g hsol).charted
    letI : IsManifold I ∞ (flowOfMetric (I := I) D P g hsol).M :=
      (flowOfMetric (I := I) D P g hsol).smooth
    letI : SigmaCompactSpace (flowOfMetric (I := I) D P g hsol).M :=
      (flowOfMetric (I := I) D P g hsol).sigmaCompact
    letI : T2Space (flowOfMetric (I := I) D P g hsol).M :=
      (flowOfMetric (I := I) D P g hsol).t2
    letI : IsManifold I 1 (flowOfMetric (I := I) D P g hsol).M :=
      IsManifold.of_le (I := I) (M := (flowOfMetric (I := I) D P g hsol).M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (flowOfMetric (I := I) D P g hsol).M := by
      change IsManifold I ∞ (flowOfMetric (I := I) D P g hsol).M
      infer_instance
    (flowOfMetric (I := I) D P g hsol).S.base.metric = g := by
  rfl

theorem flowOfMetric_atTime
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (g :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (hsol :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      letI : T2Space P.M := P.t2
      letI : IsManifold I 1 P.M :=
        IsManifold.of_le (I := I) (M := P.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
        change IsManifold I ∞ P.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := g } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := P.M) D))
    (t : Real)
    (h : g t = P.metric) :
    (flowOfMetric (I := I) D P g hsol).atTime t = P := by
  exact congrArg
    (fun m =>
      ({ M := P.M
         topology := P.topology
         charted := P.charted
         smooth := P.smooth
         sigmaCompact := P.sigmaCompact
         t2 := P.t2
         t2TangentBundle := P.t2TangentBundle
         basepoint := P.basepoint
         metric := m } : PointedRiemannianManifold.{u, uE, uH} (I := I)))
    h

end HCGCompactness
end DifferentialGeometry
