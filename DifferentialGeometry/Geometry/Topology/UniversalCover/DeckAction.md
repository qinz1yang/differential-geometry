# DeckAction

## Role

This file supplies the explicit fundamental-group deck action on the local
path-space model of the universal cover.  Its orbit theorem is the intended
producer for the fibre-identification field in later spherical quotient data.

## Route

- Prefix path classes by a loop and compute the inverse image of every
  slice-topology basic open.
- Insert an inverse when passing from path concatenation to a left action,
  because multiplication in `FundamentalGroup` uses endomorphism composition
  order.
- Prove fibre transitivity directly by the loop class `b.trans a.symm`.
- Prove smoothness from continuity and projection preservation in the pulled
  back universal-cover charts.

The pre-existing `extChartAt_proj_eq` was moved from `ChartPullback.lean` to
`Manifold.lean`: its proof only uses the universal-cover chart definition, and
the lower placement removes an unrelated nonzero-dimension assumption.

## Verification

Focused verification of `DeckAction.lean`, `Manifold.lean`, and
`ChartPullback.lean` passed.  The exact `DeckAction` module artifact and the
post-move `ChartPullback` artifact are current.  `DeckAction.lean` introduces no
`sorry`.

## Project position

The explicit deck-action producer is complete (**100%**).  It is a small,
routine part (roughly **10%**) of the dedicated global-geometry machinery still
needed by `ham3_space_box`; the theorem `ham3_space_box` itself remains
unproved (**0%**).  This work does not change the theorem-level percentage of
the broader Hamilton endpoint, which also remains **0%** while any producer in
its chain is open.

A later lane must still identify the simply connected positively curved
three-manifold with the round sphere, conjugate the action to ambient
orthogonal isometries, and package local smooth sections for the quotient.
