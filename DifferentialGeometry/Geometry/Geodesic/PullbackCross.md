# PullbackCross

## Role

This module is the canonical cross-model naturality bridge for geodesics under
a diffeomorphism equipped with the pullback metric.

## Current state

`geoEq_mapCrossAt` and `geodesicOn_mapLocal` are complete.  They consume the
pointwise along-curve naturality theorem `covAlong_natCrossAt`, identify
pushed-forward velocities as a germ by the manifold derivative chain rule, and
transfer the moving-foot geodesic equation using only a fixed `C²`
neighborhood.  Thus a geodesic and a `C∞` curve on an open time set transport
without any global curve extension.

`geoEq_mapCross`, `geodesic_mapCross`, and `geodesicOn_mapCross` remain as the
globally smooth compatibility wrappers.

Focused verification and the targeted module refresh passed without local
warnings, `sorry`, or `admit`.

The locality gap is closed and consumed by
`NormalPhaseEndpoint.normal_end_eq_intr`; cross-model geodesic naturality is no
longer on the B1 frontier.

## Project position

The cross-model geodesic naturality producer and the normal-coordinate endpoint
bridge are complete (100%).  `exists_normal_diag` now packages the quantitative
model branch and exact `diagExp` square; `normal_inv_eq` gives the compatibility
criterion with `diagExpInv`.  `StepB1RawInput` and textbook B1 remain 0%;
dedicated normal-branch machinery is about 85%, Step B/B1 infrastructure about
72%, Chapter 4 machinery about 69%, and whole HCG infrastructure about 49%.
