import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

def partitionIntervalLength {m : ℕ} (t : Fin (m + 1) → Real) (i : Fin m) : Real :=
  t i.succ - t i.castSucc

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
