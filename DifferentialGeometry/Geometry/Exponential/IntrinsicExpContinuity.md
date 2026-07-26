# IntrinsicExpContinuity.lean notes

## 2026-07-23 componentwise continuity audit

Removed the ambient `ConnectedSpace M` assumption from intrinsic-geodesic joint
continuity and `expMapIntrinsic_continuous`.  The proof is local along the
component containing the tangent-bundle input.  Focused and exact verification
passed.

Accounting: this module's no-connected migration is complete (100%).  It is
supporting infrastructure only; it does not by itself complete an HCG endpoint.
