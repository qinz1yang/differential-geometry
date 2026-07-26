# QuantCover

## Proved source boundary

`exists_ball_cover` transports the canonical quantitative Euclidean cover
from `External/DeGiorgi/FiniteCover.lean` through
`(stdOrthonormalBasis Real V).repr`.  It gives a radius-`rho` cover of a
radius-`r` closed ball with cardinality at most

`ceil ((4 * r / rho + 1)^finrank)`.

`exists_shell_cover` specializes to outer radius `(k+1) rho` and gives the
literal natural bound `(5*(k+1))^finrank`, avoiding ceilings in the Gaussian
annulus series.

This reuses the repository's existing packing/volume proof and introduces no
new geometric axiom or cover-data structure.

## Verification and frontier

Source-written while the coordinated named build was active; focused Lean
verification is pending.  The file contains no `sorry`, `admit`, axiom,
opaque declaration, or heartbeat override.

The next consumer applies this cover with `rho = sqrt t` and dyadic outer
radii.  Together with `heatKernel_early`, the polynomial cover count is
summable against Gaussian annulus decay.
