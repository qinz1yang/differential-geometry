import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.TraceFreeRicci.Norm

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F] [CompleteSpace F] [NeZero (Module.finrank Real F)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [NeZero (Module.finrank ℝ E)]
  [NeZero (Module.finrank ℝ F)] in
theorem trace_free_ricci_norm_sq_cross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M]
    [IsManifold J 1 N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (x : M) :
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAtOf
        (metricScalarAt (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x)
        (normSq0S (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          x 2
          (metricRicci (I := I)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) x)) =
      DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAtOf
        (metricScalarAt (I := J) g (Phi x))
        (normSq0S (I := J) g (Phi x) 2
          (metricRicci (I := J) g (Phi x))) := by
  rw [metricScalar_cross (I := I) (J := J),
    ricciNormSq_cross (I := I) (J := J)]

end CheegerGromovCompactness
end DifferentialGeometry
