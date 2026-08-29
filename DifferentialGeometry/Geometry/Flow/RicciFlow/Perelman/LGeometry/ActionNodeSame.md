# ActionNodeSame

## Status

`lNode_mom_same` is implemented without placeholders.  Its focused check and
targeted module refresh are GREEN and warning-free.

The theorem consumes an abstract exact two-piece action comparison rather than
global curve data.  Its conclusion identifies the terminal and initial
`chartGramOp` momenta in the common chart, with the endpoint velocities written
canonically as `derivWithin` of the two `timeH1` representatives.

## Route

Use the checked continuous momentum representative on each positive segment,
evaluate affine endpoint ramps by the generic momentum boundary identities,
and apply exact two-piece global comparison to a common scaled node
displacement.  No cotangent transition object is introduced.

The reusable `lNode_piece_min` producer is imported from `ActionNodePiece`; it
projects the exact two-piece comparison to local fixed-endpoint minimality of
each segment.  Sequential `exists_line_scale` calls keep one common nonzero
scaled displacement inside both chart tubes.  Stationarity of the sum of the
two affine action lines then gives equality against every coordinate test
vector, and `ext_inner_right` yields equality of the momenta.

## Progress

- `lNode_mom_same`: 100% source-complete and focused GREEN.
- Same-chart Weierstrass--Erdmann brick: 100%; cross-chart assembly is a
  separate downstream theorem.
- Dedicated L-geometry machinery: approximately 86%; this theorem is one node
  regularity producer, not the reduced-volume capstone.
- Generic reused infrastructure used here: 100% checked for the consumed
  `timeH1`, chart-action, force, and continuous-momentum interfaces.
- `redVolume_anti`: 0% until that theorem itself is proved.
