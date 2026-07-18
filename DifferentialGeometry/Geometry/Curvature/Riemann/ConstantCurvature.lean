import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.EinsteinMetric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

theorem einstein_of_constant_sectionalCurvature
    (g : SmoothRiemannianMetric I M) (K : Real)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      sectionalCurvatureDenominator (I := I) g p v w ≠ 0 →
        sectionalCurvature (I := I) g p v w = K) :
    DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g
      (K * ((Module.finrank Real E : Real) - 1)) := sorry

end Riemannian
end Geometry
end DifferentialGeometry
