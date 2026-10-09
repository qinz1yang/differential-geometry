import DifferentialGeometry.Tensor.Coordinates.ModelBasis
import Mathlib.Analysis.Calculus.FDeriv.Basic

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

def partialDeriv (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((chartModelBasis E) i)

end DifferentialGeometry.Tensor.Coordinates
