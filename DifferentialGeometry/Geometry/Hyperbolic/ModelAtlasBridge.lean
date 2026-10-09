import DifferentialGeometry.Geometry.Hyperbolic.Rigidity
import DifferentialGeometry.Geometry.Thurston.ConstantCurvatureAtlas

set_option autoImplicit false
noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem hasConstantSectionalCurvature.toGC
    {g : SmoothRiemannianMetric (𝓡 3) M} {K : ℝ}
    (h : hasConstantSectionalCurvature g K) :
    GC.Geometry.HasConstantSectionalCurvature g K :=
  fun p v w hvw => h p v w hvw

end DifferentialGeometry.Geometry.Hyperbolic
