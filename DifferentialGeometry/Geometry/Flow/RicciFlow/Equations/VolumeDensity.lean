import DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily


noncomputable section

namespace DifferentialGeometry

open Bundle Set
open Geometry.Curvature Geometry.Connection Geometry.Operator Integral.Measure
open Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

namespace PDE.RicciFlow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem traceTimeDerivMetric_eq_neg_two_scalar_of_ricciFlow
    (g : ℝ → SmoothRiemannianMetric I M) {t : ℝ}
    (hpde : ∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (I := I) (g t) x v w) t) (x : M) :
    traceTimeDerivMetric (I := I) g t x = -2 * metricScalarAt (g t) x := by
  classical
  have hscalar := metricScalar_chartTrace_eq (g t) x
    (self_mem_chartLeviCivitaGoodSet (I := I) (α := x))
  have hx : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  simp only [chartInvGramOnE_def, hx, chartInvGramMatrix] at hscalar
  have hd (i j : Fin (Module.finrank ℝ E)) :
      deriv (fun s => chartGramMatrix (I := I) (g s) x x i j) t =
        -2 * ricciTensor (I := I) (g t) x
          (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x) := by
    simpa only [chartGramMatrix_apply] using
      (hpde x (chartBasisVecFiber (I := I) x i x)
        (chartBasisVecFiber (I := I) x j x)).deriv
  rw [traceTimeDerivMetric_eq, Matrix.trace_mul_comm, hscalar]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, hd]
  have hsymm (i j : Fin (Module.finrank ℝ E)) :
      ((chartGramMatrix (I := I) (g t) x x)⁻¹) j i =
        ((chartGramMatrix (I := I) (g t) x x)⁻¹) i j := by
    have hh := (chartGramMatrix_isHermitian (I := I) (g t) x x).inv
    simpa only [star_trivial] using hh.apply i j
  simp_rw [hsymm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end PDE.RicciFlow

end DifferentialGeometry
