import DifferentialGeometry.Bundle.SmoothSubbundle.KernelAPI
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace Real F]

theorem hasDerivAt_apply_eq_zero_of_continuousLinearMap
    {A : Real → E →L[Real] F} {w : Real → E}
    {A' : E →L[Real] F} {w' : E} {t : Real}
    (hA : HasDerivAt A A' t) (hw : HasDerivAt w w' t)
    (hzero : ∀ s, A s (w s) = 0) :
    A' (w t) + A t w' = 0 := by
  have hprod : HasDerivAt (fun s => A s (w s))
      (A' (w t) + A t w') t := hA.clm_apply hw
  have hconst : HasDerivAt (fun _ : Real => (0 : F)) 0 t :=
    hasDerivAt_const t 0
  have hzero' : HasDerivAt (fun s => A s (w s)) 0 t := by
    simpa only [hzero] using hconst
  exact hprod.unique hzero'
