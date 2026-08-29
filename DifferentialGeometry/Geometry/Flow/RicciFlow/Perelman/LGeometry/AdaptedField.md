# `AdaptedField.lean`

## Result

`exists_lAdapted` is now proved (100%).  Given a globally smooth base curve,
an interval `Ioo a c` containing `Icc 0 b` on which `T - s^2` is regular, and
a terminal vector `V` at `alpha b`, it produces a field `P` and an open
neighborhood `Omega'` of `Icc 0 b`, contained in `Ioo a c`, such that the total
section of `P` is smooth on `Omega'`, `P b = V`, and
`D_s P = (-2 * s) RicciSharp(P)` throughout `Omega'`.

The construction fixes the terminal metric `q = g(T - b^2)`, builds a common
buffered `q`-parallel orthonormal frame by reverse-curve parallel transport,
and expands the desired field in that frame.  Its finite coefficient matrix is
the `q`-pairing with
`(-2 * s) RicciSharp(F_j) - D_s^{g(T-s^2)} F_j`; its smoothness follows from
the lower-layer `ricciSharp_chart` theorem, moving-connection regularity, and
the fixed-metric bundle inner-product API.  The parametric linear ODE solution
with terminal data given by the orthonormal expansion of `V` yields the
coefficients.  Orthonormal expansion proves both the terminal value and the
adapted ODE.  No producer assumption or wrapper frontier is introduced.

`lAdapted_inner` proves that the moving metric pairing of two fields satisfying
the square-root adapted equation
`D_s P = (-2 * s) RicciSharp(P)` has zero derivative.  The proof reuses
`lRegInner_deriv` and the native Ricci-sharp pairing identities, then performs
only the resulting scalar cancellation.

`lAdapted_inner_eq` applies the native convex-set mean-value theorem to obtain
constancy between the endpoints of any closed interval on which both fields
satisfy the adapted equation and the pointwise regularity hypotheses.

## Verification and project status

Focused verification passes without warnings or placeholders.  The
`exists_lAdapted` producer and its dedicated finite-ODE machinery are complete
(100%); this closes the adapted-field producer brick, while the explicit trace
contraction and Morgan--Tian Laplacian inequality remain unstated and unproved
(0%).
`redVolume_anti` remains unstated and unproved (0%).  Dedicated compact
ordinary-flow L-geometry machinery remains about 99%, P2 remains below 1%, and
the whole Poincare program remains approximately 3--5%.
