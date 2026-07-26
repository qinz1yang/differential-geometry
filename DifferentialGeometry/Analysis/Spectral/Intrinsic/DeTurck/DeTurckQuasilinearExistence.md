# DeTurckQuasilinearExistence

## 2026-07-14: explicit constants-first lifetime

`nemytskii_sol_const` is proved and focused verification passes.  It takes the
mixed Lipschitz constants `C1`, `C2` and a nonnegative budget `D` for
`norm (Nfun 0)` explicitly.  Its positive fixed-point lifetime is therefore an
explicit function of those three inputs.  The previous theorem
`quasilinear_maxreg_solution_of_nemytskii` remains at the same public interface
and is now a compatibility specialization using the existentially chosen
constants and the exact zero-forcing norm.

This removes an `Exists.choose` obstruction from future uniform estimates, but
does not prove C3-uniform Ricci--DeTurck existence.  The current DeTurck
nonlinearity still works at the high Sobolev order
`a = 4 * finrank E + 10`; order-at-most-three metric bounds do not control its
zero-forcing norm or mixed constants uniformly.  In addition, the current
joint-smooth realization shrinks the maximal-regularity interval to a positive
subinterval with no uniform lower bound.

Honest accounting: the low-regularity Ricci--DeTurck existence theorem is not
stated or proved (0%).  The later `LowRegCoeff` package now closes the finite
active-chart coefficient inputs from exactly the E1 `Lambda`-equivalence and
order-at-most-three intrinsic bounds.  The package now also carries a uniform
absolute RHS forcing budget, which is the `D`-type input needed by
`nemytskii_sol_const`.  Dedicated E1 machinery is about 31%, but the
low-regularity mixed `H^3 -> H^1` nonlinearity estimate, the resulting solver,
and uniform same-interval regularization remain the dominant missing analysis.
