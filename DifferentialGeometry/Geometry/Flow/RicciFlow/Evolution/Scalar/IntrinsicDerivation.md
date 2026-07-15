# IntrinsicDerivation Notes

## 2026-06-14 hcov cleanup

Removed the stale local `ConnectionLocallySmoothOn S` alias in the scalar
intrinsic derivation proof after the regular curvature-symmetry producers became
self-discharging.

Verification passed for the edited file and module refresh.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the scalar
intrinsic derivation context.  The file still checks with the existing smooth
manifold assumptions.

Verification passed for the edited file.
