import Mathlib.Data.Real.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

variable {M : Type*}

def traceFreeRicciNormSqAtOf (scalar ricciNormSq : Real) : Real :=
  ricciNormSq - scalar ^ 2 / 3

def traceFreeRicciNormSqOf
    (scalar ricciNormSq : Real -> M -> Real) (t : Real) (x : M) : Real :=
  traceFreeRicciNormSqAtOf (scalar t x) (ricciNormSq t x)

end DifferentialGeometry.PDE.RicciFlow
