import DifferentialGeometry.Geometry.Connection.MetricTrace.Iterated
import DifferentialGeometry.Geometry.Operator.Hessian.IteratedCovariantDerivative


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem normSq_hessian_metricTrace_le
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) ∞ 2) (x : M) :
    normSq0S g x 2
      (hessianSec (I := I) (leviCivitaConnectionOfMetric g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally g)
        (fun y => metricTracePair0SAt g (A y)) (trace02_smooth g A) x) ≤
      (Module.finrank ℝ E : ℝ) ^ 4 * normSq0S g x 4 (iterCov g 2 A 2 x) := by
  let B := metricTraceFirstTwoField g A
  have hB : ∀ y, B y Fin.elim0 = metricTracePair0SAt g (A y) := by
    intro y
    dsimp only [B]
    rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
      traceFirstTwo_elim0]
  have heq := iterCov_zeroTensor_two_eq_hessianSec g B
    (fun y => metricTracePair0SAt g (A y)) (trace02_smooth g A) hB
  have hbound := iterCov_metricTrace_normSq_le g A 2 x
  change normSq0S g x 2 (iterCov g 0 B 2 x) ≤
    (Module.finrank ℝ E : ℝ) ^ 4 * normSq0S g x 4 (iterCov g 2 A 2 x) at hbound
  rw [heq] at hbound
  exact hbound

theorem sqrt_normSq_hessian_metricTrace_le
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) ∞ 2) (x : M) :
    Real.sqrt (normSq0S g x 2
      (hessianSec (I := I) (leviCivitaConnectionOfMetric g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally g)
        (fun y => metricTracePair0SAt g (A y)) (trace02_smooth g A) x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        Real.sqrt (normSq0S g x 4 (iterCov g 2 A 2 x)) := by
  have hbound := Real.sqrt_le_sqrt (normSq_hessian_metricTrace_le g A x)
  have hp : (Module.finrank ℝ E : ℝ) ^ 4 = ((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 := by
    ring
  rwa [hp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)] at hbound

end DifferentialGeometry.Geometry.Operator
