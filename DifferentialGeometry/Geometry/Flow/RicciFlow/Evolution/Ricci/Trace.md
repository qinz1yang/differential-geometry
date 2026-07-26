# Trace Notes

## 2026-06-14 hcov cleanup

The regular `rm04` symmetry producers no longer accept
`ConnectionLocallySmoothOn S`; they use `connSmoothOfSol` at the regular time.
The generic arbitrary-connection symmetry APIs remain unchanged.

Verification passed for the edited file and a targeted module refresh.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the concrete
Ricci trace context.  The file checks using the already-present global smooth
manifold assumptions.

Verification passed for the edited file.
