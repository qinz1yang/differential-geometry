import DifferentialGeometry.Analysis.ODE.PhaseFlowPerturbation
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative

set_option autoImplicit false

/-!
# Free phase flow and the diagonal exponential linearization

This file identifies the analysis-layer free time-one phase map with the
continuous linear map underlying the exponential layer's unipotent
linearization.
-/

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/-- The retained-position free phase map is the linear map underlying the
unipotent diagonal-exponential derivative. -/
theorem freeDiag_eq_unip :
    PhaseFlow.freeDiag (E := E) =
      (unipotentCLE (E := E) : (E × E) →L[Real] (E × E)) := by
  apply ContinuousLinearMap.ext
  intro z
  simp [PhaseFlow.freeDiag_apply, unipotentCLE]

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
