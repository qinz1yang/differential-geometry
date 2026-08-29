# Tent variations in time H1

## Native API audit

`timeH1.ofContDiffOn` realizes globally `C¹` curves and therefore cannot
directly realize a genuine tent whose two one-sided slopes differ at the node.
`timeH1.slice` restricts and translates an existing `timeH1` curve but does not
construct a shared-node variation.  `ActionEuler` uses smooth fixed-endpoint
variations and contains no generic piecewise-affine test producer.

The lowest natural home is consequently the generic
`Analysis/Parabolic/TimeSobolev` layer.  The construction uses `timeH1.mk` and
Mathlib's native `MemLp.piecewise` for the two constant slopes; it does not add
a geometric wrapper or assume a momentum condition.

## Result

`timeH1.tent T c z` is the piecewise-affine path which is zero at times `0`
and `T` and takes the value `z` at the interior node `c`.  The API records its
piecewise formula, its two almost-everywhere constant slopes, and its initial,
node, and terminal values.

## Verification and project position

Focused verification passed without warnings.  No targeted module refresh was
run because no downstream module in this turn needs the newly exported symbols.
The source contains no `sorry`, `admit`, or axiom declaration, and all public
names are within the twenty-character limit.

This requested generic tent producer is complete (100%).  It provides all of
the test-function infrastructure for a two-segment shared-node first-variation
argument, but it proves no corner condition itself.  The Perelman
momentum-matching theorem remains unstated and therefore 0% complete; dedicated
L-geometry machinery remains roughly 86% complete, while `exists_lMinimizer`
and `redVolume_anti` remain 0% until each terminal theorem is stated and proved.
