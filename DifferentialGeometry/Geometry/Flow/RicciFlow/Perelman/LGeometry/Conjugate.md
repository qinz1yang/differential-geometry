# L-conjugate points

## Definition layer

`IsLConj` records both that `(Z, tau)` lies in the positive joint domain of
the L-exponential map and that its initial-tangent differential at `Z` is not
injective.  Keeping domain membership in the predicate prevents the totalized
off-domain value of `lExp` from creating artificial conjugate points.

The kernel-witness theorem `isLConj_iff` is finite-dimensional-free linear
algebra.  `isLConj_iff_jac` then uses the existing `lExpJacobi_eq` bridge to
identify the kernel with nonzero initial-tangent regularized L-Jacobi fields
vanishing at square-root time `sqrt tau`.  At a positive-domain nonconjugate
point, `lExpDeriv_inj` gives injectivity and `lExpDeriv_surj` uses equal finite
dimension to give surjectivity.

`lExp_localDiffeo` is the first checked L5 cut-domain producer.  It restricts
the jointly smooth positive-time L-exponential map to a fixed-time initial-
tangent slice, converts the nonconjugate differential bijection to the native
coordinate inverse-function-theorem hypothesis, and upgrades the resulting
local `C1` branch to a smooth local diffeomorphism.  No inverse branch or
cut-domain object is added as separate data.

## Verification and frontier

Focused verification passes without warnings after the local-diffeomorphism
addition.  The module contains no
`sorry`, `admit`, new axiom, reference-tree import, or additional foundational
interface.

The remaining cut-domain work is global rather than an inverse-function-
theorem gap: relate an attained minimizer to the totalized `lRegCurve`/`lExp`,
prove minimizing-prefix and first-cut alternatives, then obtain the open
star-shaped minimizing domain and the measure-zero cut image.  None of those
claims is assumed by this module.

Honest progress remains: `redVolume_anti` is unstated and unproved (0%);
the compact global-regularized-C1 minimizer endpoint is complete (100%); this
local L5 producer is complete (100%), while the global cut-domain stage is
about 5%; reusable generic prerequisites for this local producer are complete.
