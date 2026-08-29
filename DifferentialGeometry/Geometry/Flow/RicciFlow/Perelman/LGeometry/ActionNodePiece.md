# ActionNodePiece

## Status

`lNode_piece_min` projects an exact two-piece, fixed-endpoint comparison to
local fixed-endpoint minimality of either chart piece. Focused verification
passed without warnings.

## Route

The baseline coordinate image is compact and lies in the interior of its chart
target, so a sufficiently small `timeH1` neighborhood remains in the target.
Replace only the selected piece, keep the other piece fixed, and use the
competitor's fixed endpoints to preserve the shared manifold node. The
unchanged action term then cancels from the two-piece comparison.

This is a genuine local-minimality producer. It adds no variational assumption
and does not require the two pieces to use the same chart.
