import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletEigenBasis
import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralDuhamel
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def dirichletHeatSemigroup
    (g : SmoothRiemannianMetric (I_half n) M) :
    BoundedC0Semigroup
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :=
  abstractSpectralBoundedC0Semigroup (dirichletLaplacianHilbertBasis g)
    (fun i => dirichletLaplacianEigenvalue_nonneg i)

@[simp] theorem dirichletHeatSemigroup_apply
    (g : SmoothRiemannianMetric (I_half n) M) (t : ℝ) :
    dirichletHeatSemigroup g t =
      abstractSpectralSemigroup (dirichletLaplacianHilbertBasis g)
        (fun i => dirichletLaplacianEigenvalue_nonneg i) t :=
  rfl

def dirichletHeatDuhamel
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (F : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (t : ℝ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  abstractSpectralDuhamel (dirichletLaplacianHilbertBasis g)
    (fun i => dirichletLaplacianEigenvalue_nonneg i) u₀ F t

theorem dirichletHeatDuhamel_repr_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    {F : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)}
    (hF : Continuous F) {t : ℝ} (ht : 0 ≤ t)
    (i : DirichletLaplacianEigenIndex g) :
    ((dirichletLaplacianHilbertBasis g).repr
      (dirichletHeatDuhamel g u₀ F t) : DirichletLaplacianEigenIndex g → ℝ) i =
      Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
          ((dirichletLaplacianHilbertBasis g).repr u₀ :
            DirichletLaplacianEigenIndex g → ℝ) i +
        ∫ τ in (0 : ℝ)..t,
          Real.exp (-(dirichletLaplacianEigenvalue i) * (t - τ)) *
            ((dirichletLaplacianHilbertBasis g).repr (F τ) :
              DirichletLaplacianEigenIndex g → ℝ) i := by
  exact abstractSpectralDuhamel_repr_apply
    (dirichletLaplacianHilbertBasis g)
    (fun i => dirichletLaplacianEigenvalue_nonneg i) u₀ hF ht i

theorem dirichletHeat_mild_solution_exists
    (g : SmoothRiemannianMetric (I_half n) M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (F : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (hF : Continuous F) :
    ∃ T : ℝ, ∃ u : ℝ →
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g),
      DifferentialGeometry.PDE.IsLinearTensorParabolicMildSolution
        (dirichletHeatSemigroup g) u₀ F T u := by
  exact DifferentialGeometry.PDE.linear_tensor_parabolic_shortTime_exists
    (dirichletHeatSemigroup g) u₀ F hF

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry
