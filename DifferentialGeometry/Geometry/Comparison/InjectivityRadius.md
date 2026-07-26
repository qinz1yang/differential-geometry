# InjectivityRadius

## Status

The injectivity radius now measures injectivity of the actual orthonormally
framed exponential map

The injectivity API now also exposes `exp_dom_of_inj` and
`exp_dom_of_inj_rad`.  They record the non-circular consequence needed by the
H6 audit: injectivity on a framed model ball forces that ball into the natural
`expDomain`, since the totalized exponential takes the center value outside
the domain.  This does not claim containment in the qualitatively selected
`framedExpDiffeo.source` and does not supply smoothness away from its source.
The extended source passes its focused check; the previously exported
injectivity-radius API remains target-checked.

`z |-> exp_p (normalFrame g p z)`

on model balls. By `normalFrame_sqrt`, these are exactly intrinsic `g_p`
tangent balls. The focused check and exact module refresh pass.

The two low-level raw `expMapDiffeo` source lemmas remain available for the
Gauss radius construction. They live in a separate `RawExpMap` section with
the legacy explicit `NormedSpace` / `Module.Finite` signature. This separation
is required: otherwise Lean elaborates the public theorem against
`InnerProductSpace.toNormedSpace`, which does not match older callers whose
`ModelWithCorners` was formed with an explicitly supplied normed-space
instance.

## Next Consumer

The framed Chapter-4 migration is complete.  The next native consumer is the
quantitative H6 branch: combine `exp_dom_of_inj_rad` with an off-zero
smoothness/local-diffeomorphism theorem on the natural exponential domain.
That theorem is not currently present; do not replace it by containment in the
arbitrarily selected `framedExpDiffeo.source`.
