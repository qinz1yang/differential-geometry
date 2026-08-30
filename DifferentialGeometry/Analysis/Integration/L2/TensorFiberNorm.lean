import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs

noncomputable section

open Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : ∀ x, TensorRSSpace r s I x) :
    tensorL2Norm (I := I) (M := M) g r s
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
            (r := r) (s := s) (x := x) (T x)) ^ 2
      = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (T x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorL2Norm_def, Real.sq_sqrt (by
        unfold tensorL2Inner
        refine integral_nonneg (fun x => ?_)
        exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _)]
  unfold tensorL2Inner
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (T x)).symm

end Elliptic
end Analysis
end DifferentialGeometry

end
