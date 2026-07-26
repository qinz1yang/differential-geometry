# RicciConnection.lean

## 2026-07-17 curvature-operator symmetry

Added `riemannOp_diag_symm`, the metric self-adjointness identity for the
curvature operator with the two repeated geodesic-velocity slots.  It is the
curvature cancellation used to prove that the Wronskian of two Jacobi fields
has zero derivative.

The explicitly named module build passed.  A direct focused source check hit a
pre-existing heartbeat timeout in this large module, so the targeted build is
the successful verification evidence for this addition.
