import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.AllScales
import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric
import DifferentialGeometry.Geometry.Metric.Completeness

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M]

def CurvatureOperatorNonnegative
    {T : Real}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T)) : Prop :=
  ∀ t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T).carrier,
    ∀ x : M,
      (⟨S.base.rm04 t x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)

structure KappaSolution
    {T kappa : Real}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T)) : Prop where
  nonempty : Nonempty M
  connected : ConnectedSpace M
  isSolution : IsSolutionOn (I := I) S
  complete : ∀ t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T).carrier,
    DifferentialGeometry.RiemannianMetricComplete (I := I) (S.base.metric t)
  curvatureOperator_nonnegative : CurvatureOperatorNonnegative (I := I) S
  kappa_pos : 0 < kappa
  noncollapsed : KappaNoncollapsedOnAllScales S kappa
  bounded_curvature :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T).carrier,
        ∀ x : M, FlowMetricBall.rmNormSq S t x ≤ C
  nonflat :
    ¬ (∀ t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T).carrier,
      ∀ x : M, S.base.rm04 t x = 0)

theorem KappaSolution.curvatureOperator_nonnegative_at
    {T kappa : Real}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T)}
    (hS : KappaSolution (I := I) (kappa := kappa) S)
    {t : Real} (ht : t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T).carrier)
    (x : M) :
    (⟨S.base.rm04 t x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ :
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :=
  hS.curvatureOperator_nonnegative t ht x

theorem KappaSolution.has_curvature_bound
    {T kappa : Real}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T)}
    (hS : KappaSolution (I := I) (kappa := kappa) S)
    {t : Real} (ht : t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T).carrier) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x : M, FlowMetricBall.rmNormSq S t x ≤ C := by
  rcases hS.bounded_curvature with ⟨C, hC, hbound⟩
  exact ⟨C, hC, fun x => hbound t ht x⟩

theorem KappaSolution.has_global_curvature_bound
    {T kappa : Real}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T)}
    (hS : KappaSolution (I := I) (kappa := kappa) S) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T).carrier,
        ∀ x : M, FlowMetricBall.rmNormSq S t x ≤ C :=
  hS.bounded_curvature

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
