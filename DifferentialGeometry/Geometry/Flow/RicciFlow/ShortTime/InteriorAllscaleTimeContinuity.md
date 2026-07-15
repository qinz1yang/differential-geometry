# InteriorAllscaleTimeContinuity

## 2026-07-14: remove the deferred local-Weyl dependency

`interior_allscale_time_continuity` only needs eigenvalue-tail summability for
the `(0,2)` connection-Laplacian spectrum. It now obtains that input directly
from the proved non-sharp global Weyl producer `tensorEigen_summable_negpow`, at
the explicit exponent `weylSobolevExp + 1`.

This removes the theorem's dependency on the deferred, substantially stronger
pointwise local-Weyl statement in `WeylEigenvalueCountingBound.lean`. It does not
claim that the latter statement has been proved. Focused verification is pending.

The endpoint theorem remains fully stated and proved; this change only replaces
one analytic producer in its dependency chain.
