# CoordinateIdentities Notes

## 2026-06-14 hcov cleanup

Removed obsolete `ConnectionLocallySmoothOn` threading from the coordinate
Ricci-evolution path and from the regular curvature-symmetry calls.  Regular
symmetry producers now discharge solution-connection smoothness internally.

Verification passed for the edited file.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the concrete
Ricci coordinate identity file.  No public API here needs to expose that
equivalent spelling of smoothness.

Verification passed for the edited file.
