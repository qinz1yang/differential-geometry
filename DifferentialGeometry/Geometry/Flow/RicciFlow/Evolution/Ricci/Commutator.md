# Commutator Notes

## 2026-06-14 hcov cleanup

Updated the Levi-Civita/solution contracted-commutator wrapper to consume the
self-discharging regular curvature-symmetry producers instead of threading
`ConnectionLocallySmoothOn S`.

Verification passed for the edited file.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the concrete
Ricci commutator context.  The remaining smoothness requirements are supplied
by the standard global manifold context.

Verification passed for the edited file.
