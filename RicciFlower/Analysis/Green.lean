import RicciFlower.Analysis.DivergenceTheorem.Family

set_option autoImplicit false

/-!
# RicciFlower Green and integration-by-parts entrypoint

This module exposes the RicciFlower-native port of the closed-manifold
Divergence Theorem / Green identity stack from the local measure reference tree.
The canonical theorem handles live under
`RicciFlower.Analysis.DivergenceTheorem`.
-/

namespace RicciFlower
namespace Analysis
namespace Green

export RicciFlower.Analysis.DivergenceTheorem
  (integral_divergence_eq_zero_of_compact
   integral_tangentSectionAction_eq_neg_integral_smul_divergence
   integral_inner_grad_eq_neg_integral_smul_laplacian
   integral_smul_laplacian_sub_eq_zero
   expNegLap_eq_gradSq
   expNegIBP)

end Green
end Analysis
end RicciFlower
