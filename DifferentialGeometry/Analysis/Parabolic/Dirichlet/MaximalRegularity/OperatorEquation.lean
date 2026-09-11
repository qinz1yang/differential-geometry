import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity.Operator
import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Laplacian

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Dirichlet
namespace MaximalRegularity

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
  (perModeConvolutionDerivL2_apply)
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {g : SmoothRiemannianMetric (I_half n) M}
variable {a T : ℝ}

def timeDirichletHsLaplacian (g : SmoothRiemannianMetric (I_half n) M)
    (a : ℝ) {T : ℝ} :
    timeL2 (DirichletHs g (a + 2)) T →L[ℝ]
      timeL2 (DirichletHs g a) T :=
  (dirichletHsLaplacian g a).compLpL 2 (timeMeasure T)

theorem timeDirichletHsLaplacian_coeFn
    (v : timeL2 (DirichletHs g (a + 2)) T) :
    timeDirichletHsLaplacian g a v =ᵐ[timeMeasure T]
      fun t => dirichletHsLaplacian g a (v t) :=
  (dirichletHsLaplacian g a).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) v

theorem timeModeCoeff_timeDirichletHsLaplacian
    (v : timeL2 (DirichletHs g (a + 2)) T)
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff (timeDirichletHsLaplacian g a v) i =
      (-dirichletLaplacianEigenvalue i) • timeModeCoeff v i := by
  refine Lp.ext ?_
  have hlhs := timeModeCoeff_coeFn
    (timeDirichletHsLaplacian g a v) i
  have hΔ := timeDirichletHsLaplacian_coeFn v
  have hsmul := Lp.coeFn_smul (-dirichletLaplacianEigenvalue i)
    (timeModeCoeff v i)
  have hvcoe := timeModeCoeff_coeFn v i
  filter_upwards [hlhs, hΔ, hsmul, hvcoe] with t ht hΔt hsmt hvt
  rw [ht, hΔt, dirichletHsLaplacian_coeff, hsmt, Pi.smul_apply, hvt,
    smul_eq_mul]

theorem maximalRegularityOp_solves_perMode (hT : 0 ≤ T)
    (f : timeL2 (DirichletHs g a) T)
    (i : DirichletLaplacianEigenIndex g) :
    timeModeCoeff (maximalRegularityDerivField a hT f) i =
      (-dirichletLaplacianEigenvalue i) •
          timeModeCoeff (maximalRegularitySolField a hT f) i +
        timeModeCoeff f i := by
  rw [maximalRegularityDerivField_timeModeCoeff (a := a) hT f i,
    maximalRegularitySolField_timeModeCoeff (a := a) hT f i]
  rw [derivModeCoeff, perModeConvolutionDerivL2_apply, solModeCoeff, neg_smul,
    ← sub_eq_neg_add]

theorem maximalRegularityOp_solves
    (hT : 0 < T)
    (f : timeL2 (DirichletHs g a) T) :
    TimeSobolev.timeH1.timeDeriv _ T
        (maximalRegularityOp a hT f) =
      timeDirichletHsLaplacian g a
          (maximalRegularitySolField a hT.le f) + f := by
  rw [maximalRegularityOp_timeDeriv (a := a) hT f]
  refine timeModeCoeff_injective (fun i => ?_)
  rw [timeModeCoeff_add,
    timeModeCoeff_timeDirichletHsLaplacian
      (a := a) (maximalRegularitySolField a hT.le f) i]
  exact maximalRegularityOp_solves_perMode (a := a) hT.le f i

end MaximalRegularity
end Dirichlet
end Parabolic
end Analysis
end DifferentialGeometry
