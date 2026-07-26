# `ChartWkpMorrey.lean`

## Source theorem

`w3p_morrey_c2` is the concrete local supercritical bridge used by the
dimension-general contraction route.  If `p > d`, a scalar `W^{3,p}` chart
component on a ball has a `C^2` representative on the quarter ball.  Every
coordinate component of its second derivative is Hölder with exponent
`1 - d/p` on the next quarter ball, with a fixed dimension/exponent constant
times the original `W^{3,p}` norm.

The proof does not assume that weak chart arrays are free.  It identifies the
order-two weak partials of the `C^2` representative with their classical
partials, applies the canonical scalar Morrey theorem to each true
`W^{1,p}` second weak partial, and upgrades a.e. equality to pointwise equality
using continuity and positivity of Euclidean volume on open sets.

## Verification state

Source written and statically inspectable; focused Lean verification is
pending while the shared named build owns the build lane.  Endpoint theorem
credit remains 0% until verification.
