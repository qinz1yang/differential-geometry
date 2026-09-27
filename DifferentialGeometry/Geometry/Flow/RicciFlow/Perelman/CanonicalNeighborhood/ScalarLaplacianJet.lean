import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ShiUniformConstant
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M]

variable [NeZero (Module.finrank ℝ E)]

theorem scalarLaplacianCurvatureJetBound :
    ScalarLaplacianCurvatureJetBound.{u, uE, uH} I ((Module.finrank ℝ E : ℝ) ^ 6) := by
  intro M _ _ _ _ _ _ _ D S _ t _ x
  exact abs_laplacian_scalar_le_second_curvature S t x

theorem goodPointBoundsOn_of_modelBound [I.Boundaryless] {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, uE, uH} I kappa) :
    ∃ CStar : ℝ, 0 ≤ CStar ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
        [VectorBundle ℝ E (TangentSpace I : M → Type _)]
        {T : ℝ} {hT : (0 : ℝ) < T}
        (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
        IsSolutionOn (I := I) S → ∀ (x : M) (t eps : ℝ), 0 < eps → eps ≤ 1 / 4 →
          IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t →
            (∀ v : TangentSpace I x,
                |scalarDifferential (I := I) S t x v| ≤
                  2 * CStar * (S.scalar t x * Real.sqrt (S.scalar t x)) *
                    Real.sqrt ((S.base.metric t).inner x v v)) ∧
              |deriv (fun tau : ℝ => S.scalar tau x) t| ≤ CStar * S.scalar t x ^ 2 :=
  goodPointBoundsOn_of_modelCurvatureBound I (by positivity) hmod
    witnessSourceBallCapture (localShiUniformConstant I) scalarLaplacianCurvatureJetBound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
