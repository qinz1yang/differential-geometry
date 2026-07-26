# TimeInterval notes

## 2026-07-17 regular compact windows

Added `RealTimeInterval.exists_Icc_regular`.  It records the local consequence
of the existing openness field that every regular time is interior to a closed
real interval still contained in the regular set.  The proof reuses Mathlib's
neighborhood interval basis; no new interval assumption or global exhaustion
predicate is introduced.

This is the correct local input for upgrading a fixed-window Ricci-flow PDE
from `HasDerivWithinAt` to `HasDerivAt`.

## 2026-07-17 canonical open-interval exhaustion

Added `openWindowLeft`, `openWindowRight`, and `openWindow`, together with the
checked containment, initial-time membership, nesting, point-membership, and
union-exhaustion lemmas.  These are the canonical compact windows for the
book-facing `openInterval a b t₀` route.  Each window contains `t₀`, lies
strictly inside `(a,b)`, and the increasing union is all of `(a,b)`.

This removes any need for a new `HasWindowExhaustion` predicate in MSM135
Theorem 3.10.  It does not assert convergence or choose a subsequence; the P4
producer must still diagonalize the fixed-window analytic outputs.

Added the checked `exists_window_superset` compactness bridge.  Any closed
interval contained in `(a,b)` is absorbed by one canonical window (including
the vacuous reversed-endpoint case).  This is the exact routing lemma needed
to turn window-indexed convergence into convergence on an arbitrary compact
time interval; it adds no hypothesis to the compactness endpoint.

Added the checked `exists_window_nhds` pointwise bridge.  Every point of the
open interval has one canonical closed window as a neighborhood.  This is the
precise fact used to upgrade a derivative within that window to an ordinary
derivative, and it also lets pointwise scalar convergence select a local
window without assuming the whole open interval lies in one closed window.
