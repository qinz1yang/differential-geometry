# Minimizing regularized L-curves

## Implemented surface

`lCost` is the raw L-length infimum over square-root reparameterizations of
global regularized `C¹` curves with fixed endpoints.  It selects the exact
competitor category constructed by the direct-method modules without adding a
new admissible-path structure.

`lRegIndex_nonneg_var` proves nonnegativity for the transverse field of a
supplied smooth fixed-endpoint variation when its parameterized regularized
action has a genuine local minimum.

`lRegIndex_nonneg` upgrades this to every globally `C^8` tangent field along
the central regularized L-curve that vanishes at both endpoints. Its minimizing
hypothesis states directly that regularized action has a local minimum along
every smooth fixed-endpoint variation of the curve; it is not a supplied
semidefiniteness assumption or a frontier wrapper.

The proof realizes the field by the generic compactly supported geodesic-spray
flow, applies the variation-level second-derivative theorem, and then uses
`lRegIndex_congr` on the open interval. This last step handles endpoint
derivatives honestly rather than rewriting them from closed-interval equality.

## Verification and next frontier

Focused verification passes without warnings.  The arbitrary-field index
nonnegativity theorem and `lCost` are complete.  The subsequent direct-method,
finite-node, classical Euler, and endpoint-extension modules now prove the
compact positive-time endpoint `exists_lMinimizer`: an endpoint-honest
`IsLRegCurveOn` whose square-root reparameterization realizes `lCost` and
beats every global regularized C1 fixed-endpoint competitor.

The theorem deliberately does not claim a broader AC or piecewise-C1
competitor category.  The next L5 work is no longer existence: it is the
unique-minimizing/cut-domain geometry and the measure-zero cut-locus statement
needed to globalize reduced length.

`redVolume_anti` remains unstated and unproved at **0%**;
`lRegIndex_nonneg_var` and `lRegIndex_nonneg` are **100%**;
the compact global-regularized-C1 `exists_lMinimizer` is **100%**;
`redVolume_anti` remains **0%**.  Dedicated minimizer machinery and reused
generic prerequisites for this endpoint are **100%**.  P2 remains below 1%,
and the full Poincare program remains approximately **3--5%**.
