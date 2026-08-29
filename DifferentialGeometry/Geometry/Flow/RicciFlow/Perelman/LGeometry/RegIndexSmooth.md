# RegIndexSmooth

## Scope

This module supplies the native analytic producer for the regularized L-index
density. `lRegIndex_intOn` is the local form used by canonical strict rays: it
requires `C^2` total sections only on an open neighborhood of `uIcc a b`.
`lRegIndex_int` remains the global convenience wrapper. Smoothness of `alpha`
is recovered from either total section, so it is not a redundant public
hypothesis.

## Native route

The only nonstandard step is continuity of the moving covariant derivatives.
At each parameter it fixes the tangent-bundle trivialization centered at the
current base point, differentiates the local representative of the `C^2`
section, and combines it with the jointly continuous Christoffel symbols of the
Ricci-flow metric. The proof then returns to the total tangent bundle via
`covDerivAlong_chart_foot_invariance`; it never unfolds or compares whole
bundle or Hom representations.

The remaining four scalar terms use existing native family-evaluation APIs for
the metric, `rm04`, the scalar Hessian, and the covariant derivative of Ricci.
Thus `C^2` is sufficient; no `C^8` assumption is needed.

`chartRep_diff_at` is the weakest pointwise producer: `C^2` regularity of the
total tangent-bundle section at one parameter gives differentiability there of
its fixed-base chart representative.  `chartRep_diff_two` is the global `C^2`
companion and now delegates to this pointwise theorem.  The L-cost Hessian
comparison uses the lower-order form for the difference between a supplied
`C^8` comparison field and the canonical L-Jacobi field; it therefore does not
strengthen that consumer to `C^infty`.

## Verification and status

Focused verification passes without warnings after exporting
`chartRep_diff_at` and refactoring `chartRep_diff_two` through it; the earlier
exported-module refresh also passed after the redundant curve-smoothness
hypothesis was removed.

- `lRegIndex_intOn`: 100% implemented, exported, and focused-verified.
- `lRegIndex_int`: 100% implemented and verified.
- `chartRep_diff_at`: 100% implemented, exported, and focused-verified.
- `chartRep_diff_two`: 100% implemented, exported, and focused-verified.
- This dedicated producer lane: 100%.
- The downstream `redVolume_anti` capstone is now proved separately; this file
  remains an analytic producer rather than claiming that endpoint.
- Dedicated compact ordinary-flow L-geometry machinery is about 99%, including
  the separate small-time normalization follow-up.
- Reused generic geometric regularity infrastructure: 100% for this route and
  not counted as completion of `redVolume_anti`.
- P2 remains below 1%; the whole Poincare program remains about 3--5%.
