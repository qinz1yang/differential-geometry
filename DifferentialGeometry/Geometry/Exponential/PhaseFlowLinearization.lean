import DifferentialGeometry.Analysis.ODE.PhaseFlow.Perturbation
import DifferentialGeometry.Geometry.Exponential.DiagonalExponentialDerivative
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace PhaseFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

theorem freeDiag_eq_unipotent :
    freeDiag (E := E) =
      (Geometry.Riemannian.Exponential.unipotentCLE (E := E) :
        (E × E) →L[Real] (E × E)) := by
  apply ContinuousLinearMap.ext
  intro z
  simp [freeDiag_apply, Geometry.Riemannian.Exponential.unipotentCLE]

end PhaseFlow
end DifferentialGeometry
