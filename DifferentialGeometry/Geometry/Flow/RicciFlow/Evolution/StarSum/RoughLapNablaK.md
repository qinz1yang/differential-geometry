# RoughLapNablaK Notes

## 2026-06-14 hcov/hmc cleanup

The solution-specific rough-Laplacian/spatial-commutator lemmas now derive
local smoothness and metric compatibility internally from the metric connection.
No generic arbitrary-connection API was weakened.

Verification passed for the edited file.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the concrete
rough-Laplacian/nabla-k context.  The file checks with the global smooth
manifold instance.

Verification passed for the edited file.
