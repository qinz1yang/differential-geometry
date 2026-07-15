# RingInverseDeriv

## Role

This module is the canonical Banach-algebra calculus layer for derivatives of
`Ring.inverse`.  It was extracted from the Step C consumer so H6 and other
geometric producers can reuse the same estimates without a parallel API.

## Current state

- `contDiffOn_ringInverse` records smoothness on the unit group.
- `norm_iteratedFDerivWithin_ringInverse_le` gives the all-order within-set
  inverse derivative estimate.
- `norm_iteratedFDeriv_ringInverse_le` is the pointwise full-derivative form.
- `norm_iteratedFDeriv_invComp_le` combines inversion with a smooth map through
  the existing Faà-di-Bruno estimate.

Focused verification and the targeted module build passed.  The module has no
remaining proof frontier.
