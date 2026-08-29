# C1 approximation of time-H1 tents

## Native route

The construction reuses the existing generic APIs rather than introducing a
new joining object.  It takes the two `timeH1.slice`s of `timeH1.tent` on
`[0,c]` and `[c,T]`, applies `exists_flat_dense` to each slice, translates the
right representative back to the original time variable, and glues the two
representatives with `contDiffOn_Icc_join`.

The flat endpoint germs supplied by `exists_flat_dense` are essential: both
pieces are identically equal to the prescribed node value near `c`.  Hence the
assembled representative has an actual constant germ at the node, so its two
one-sided derivatives agree without a supplied matching assumption.

`deriv_ae_of_eqOn` is the small missing representation bridge.  It identifies
the weak derivative of a `timeH1` curve with the ordinary derivative of a
global `C¹` representative that agrees with its continuous representative on
the compact time interval.

## Result

`exists_tent_c1` produces `C¹` closed-interval representatives of the tent
with exact values `0`, `z`, and `0` at times `0`, `c`, and `T`.  The associated
`timeH1` curves converge strongly to the tent, and their weak derivatives
converge strongly in `timeL2` to the tent derivative.

The strong derivative convergence is proved by an exact decomposition of its
L2 error square into the left-slice and right-slice error squares.  The right
term is transported by the native interval-integral translation identity.

## Verification and project position

Focused verification passed without warnings.  No targeted refresh was run
because no downstream module in this turn immediately consumes the new
exports.  The source has no `sorry`, `admit`, or new axiom declaration, and
both public names fit the twenty-character limit.  The axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

This generic approximation brick is complete (100%).  The final Perelman
momentum-matching/corner theorem remains unstated and therefore 0% complete;
its dedicated shared-node test-function machinery is now roughly 75% complete.
Dedicated L-geometry machinery remains roughly 86% complete, while
`redVolume_anti` remains 0% until that terminal theorem is proved.  Generic
infrastructure reused by this brick is complete for its stated role.
