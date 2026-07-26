# GammaCoord Notes

## 2026-06-14 hcov cleanup

The Ricci-variation coordinate producers no longer carry a caller-supplied
local-smoothness witness for the solution connection.  They derive it internally
from `connSmoothOfSol`.

Verification passed for the edited file.

## 2026-06-14 manifold instance cleanup

Removed the redundant explicit `infty+1` manifold binder from the concrete
Ricci-flow coordinate producer context.  The global smooth manifold instance
already supplies the needed regularity.

Verification passed for the edited file.
