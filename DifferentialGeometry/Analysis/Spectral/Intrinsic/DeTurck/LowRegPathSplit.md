# LowRegPathSplit

## Purpose

This module isolates the genuinely low-regularity top arm of the
three-dimensional Ricci--DeTurck remainder.  It separates the small varying
cometric coefficient from the fixed curvature commutator and targets the
spectral `H3 -> H1` estimate needed at maximal-regularity order one.

## Current route

The already checked `top_path_split`, `fixed_curv_h1`, and `top_path_h1`
reduce the top arm to a two-jet coefficient deviation plus a fixed
`H2 -> H1` curvature term.

The new source-level chain is:

- `phi_dev_h2`: combines `inv_coeff_h2` with the explicit trace-Hessian and
  Ricci-principal coefficient bounds to control the total top coefficient at
  every point of a convex `H2` path;
- `top_path_dev_h2`: transfers the same pointwise/two-jet bound through the
  path integral;
- `top_path_ball_h1`: feeds that producer into `top_path_h1`, removing the
  external coefficient-envelope hypotheses from the actual top-arm estimate.

This route uses only three-dimensional small spectral `H2` data for the
varying principal coefficient.  It does not invoke the high-order
`a >= 2 * dim + 10` ball theorem.

## Verification and frontier

The complete source-level chain now passes focused verification with no
warnings and no `sorry`. In particular, the varying top coefficient is
controlled using only the three-dimensional spectral `H2` ball, and the fixed
curvature commutator loses exactly the two derivatives already budgeted by the
`H3 -> H1` remainder estimate. A small private linearity lemma for
`reindexCoeffGen` exposes the coefficient difference before additive-group
normalization.

### Historical pre-extraction frontier

At this checkpoint the remaining mixed remainder work was the separated
order-one and order-zero path arms, followed by the low-regularity parabolic
solver and same-interval regularization.  The route-A migration and 2026-07-18
ruling below supersede this description.

The live high-regularity source contains the exact three-arm path identity,
but both that theorem and its order-zero/order-one path coefficients are
private, while the public wrapper combines the identity with the unusable
`a >= 2 * dim + 10` envelope. The next structural producer must expose the
exact full principal cancellation and the order-zero/order-one branch without
coupling it to that envelope. The concrete path objects live in a source file
far above the 3000-line maintenance limit, so adding a facade there is not an
admissible route. The unresolved architecture choice is between extracting
that construction into a small module and integrating the public metric-family
chart linearization into `RHSSectionCovGradL2Decomposition`; a read-only
consult did not return a ruling. Merely exporting an existential equality would
not expose enough coefficient data for the `LowRegCoeff` bounds.

At this checkpoint uniform low-regularity Ricci--DeTurck existence and
`ricci_flow_unif_existence` were theorem-level 0%.  The top-arm theorem was
proved; the unconditional mixed `H3 -> H1` remainder theorem was unstated and
therefore theorem-level 0%.  The later conditional theorem
`rem_h1_of_bounds` does not change that unconditional accounting.

## 2026-07-16 route-A migration

The architecture choice is now settled and implemented as route A. The exact
Ricci+DeTurck three-arm cancellation and its concrete path integrals were
extracted into small public modules. Every top-path occurrence in this module
now uses `DeTurckCoefficients.rhsTopPathIntegral`; the old oversized remainder
file is absent from this import chain.

At this historical checkpoint the migrated source had not yet received its
final focused check.  The approximately 78% machinery figure is superseded by
the later route ruling.

## 2026-07-18 verification repair

The migrated proof uses
the reindexing form of `deTurckPhiMetTotal`, but the dependency split had left
that algebraic identity private to the oversized high-order remainder module.
The identity is now the small canonical theorem `phiMet_reindex` in
`DeTurckTopCoeff`; this module consumes it through the existing small import
boundary.  No import of `DeTurckRemainderTameLipschitz` is needed.  The final
focused source check passes without local warnings or `sorry`s, and the named
downstream target refresh succeeds.  The top-arm chain is 100%; the
unconditional mixed theorem and uniform-existence endpoint remain 0%.
