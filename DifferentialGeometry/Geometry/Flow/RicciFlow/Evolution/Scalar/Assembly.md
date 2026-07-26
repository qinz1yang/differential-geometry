# Assembly Notes

## 2026-06-14 hcov cleanup

Removed the local `ConnectionLocallySmoothOn S` alias from the scalar assembly
wrapper after the Ricci trace/curvature symmetry producers were made
self-discharging for solution connections.

Verification passed for the edited file.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the scalar
assembly wrapper.  The proof checks with the global smooth manifold context.

Verification passed for the edited file.
