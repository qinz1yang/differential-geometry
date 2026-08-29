# Interior regularity of finite L-action minimizers

## Result

`lMinCurve_reg` compresses an arbitrary monotone finite chart realization of a
global fixed-endpoint minimizer to a strict positive subdivision with
`exists_lStrict`.  The endpoint identities and `a < b` rule out the zero-piece
case.  It then applies `lStrict_curve_reg`, so every point of `Ioo a b` has the
full intrinsic regularized L-geodesic triple: manifold differentiability,
differentiability of the chart representative of the actual `lVelocity`, and
the intrinsic acceleration equation.

No finite witness, node equation, or regularity conclusion is added as an
assumption.

## Verification

Focused verification and the targeted module refresh passed without warnings
or placeholders.

The noncompact declaration-level generalization passed focused verification
without warnings after the shared guard cleared. `lMinCurve_reg` now exports
without an ambient `CompactSpace M` instance; its downstream refresh also
passed.

## Project position

This theorem is the arbitrary-monotone interior regularity consumer.  The
terminal `exists_lMinimizer` and `redVolume_anti` remain unproved at 0%; their
dedicated L-geometry machinery is about 98%, while the generic infrastructure
used here is complete.
