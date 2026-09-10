import DifferentialGeometry.Geometry.Curvature.Metric.Defs

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

def isGradientRicciSoliton
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ) : Prop :=
  ∀ x : M,
    metricRicciAt (I := I) g x +
      hessianSec (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g)
        f f.contMDiff x =
      (σ / 2) • metricTensor0S (I := I) g x

end DifferentialGeometry.Geometry
