# LipschitzW1

## 2026-07-16 Euclidean entrance producer

The cutoff audit found that the vendored Rademacher API already proves the
distributional integration-by-parts identity needed by `HasWeakPartialDeriv`.
The shortest native route uses `lineDeriv` rather than first constructing a
globally selected a.e. Frechet derivative.

`hasWeakPart_of_lip` identifies each coordinate line derivative as a weak
partial derivative on an arbitrary set. `memW1p_of_lip` and
`memWkp_one_of_lip` then package global Lipschitz continuity and compact
support into first-order Euclidean Sobolev membership. This is genuine
producer infrastructure; it does not add a cutoff assumption or move the
analytic content into a consumer wrapper.

`lip_of_local_comp` supplies the final local-to-global step used by chart
cutoffs: a locally Lipschitz Euclidean function with compact support and a
global amplitude bound is globally Lipschitz.  Its proof takes a compact
closed thickening of the support, obtains one Lipschitz constant there, and
uses the amplitude bound for pairs that cross the thickening boundary.  This
avoids choosing finitely many local constants by hand.

The remaining Noncollapsing frontier is geometric and quantitative: prove
that each compactly supported chart pushforward of the intrinsic distance
tent is globally Lipschitz with constants controlled well enough to retain a
ball-volume energy bound. In particular, a metric-dependent chart constant
must not be treated as uniform along a potentially singular sequence of flow
times without a separate uniform comparison theorem.

Focused verification passed without warnings.

## 2026-07-17 classical-to-weak derivative bridge

`fderiv_ae_chosen` now identifies the classical coordinate derivative of a
globally Lipschitz compactly supported function with `chosenWeakPartial'`
almost everywhere on any open set.  The proof combines Rademacher,
`hasWeakPart_of_lip`, local integrability, and uniqueness of weak partials.
This is the lowest-layer reusable bridge required by the finite-POU
chart-to-intrinsic gradient comparison; it avoids duplicating the argument in
the intrinsic consumer.

The first focused check found only an application-shape mismatch:
`DifferentiableAt.lineDeriv_eq_fderiv` infers its direction from the goal and
must not be applied explicitly.  After using the inferred equality, focused
verification passed without warnings.

## 2026-07-17 quantitative L2 bridge

`partials_l2_le_wkp` upgrades the preceding a.e. identification to the exact
quantitative estimate needed by the nonsmooth chart-to-intrinsic comparison:
the `L²` norm of the Euclidean length of all classical coordinate partials is
bounded by `wkpNorm 1 2`.  The proof uses only the finite-dimensional triangle
estimate, `fderiv_ae_chosen`, and the order-one block already present in the
definition of `wkpNorm`; no smoothness assumption is reintroduced.

Focused verification passed.  This closes the Euclidean producer; the
remaining frontier is the manifold finite-POU and measure-bridge assembly.
