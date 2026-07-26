import DifferentialGeometry.Tensor.RicciIdentity.OneForm
import DifferentialGeometry.Tensor.RicciIdentity.Tensor0S.Realization
import DifferentialGeometry.Tensor.RicciIdentity.Tensor0S.Formula
import DifferentialGeometry.Tensor.RicciIdentity.MixedComponents

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Tensor Ricci Identity Compatibility Wrapper

Thin umbrella that re-exports the tensor Ricci-identity API
(`DifferentialGeometry.Tensor.RicciIdentity.*`) for the realized Ricci-flow
layer.
-/
