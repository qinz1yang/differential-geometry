# Lichnerowicz Notes

## 2026-06-14 hcov cleanup

Removed caller-facing solution local-smoothness aliases from the Lichnerowicz
coordinate wrappers.  The downstream regular curvature producers now provide the
needed smoothness internally.

Verification passed for the edited file.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the concrete
Lichnerowicz/Ricci evolution context.  The checked proofs only need the global
smooth manifold instance already in scope.

Verification passed for the edited file.
