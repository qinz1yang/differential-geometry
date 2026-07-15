# CLMNeumann

## Role

This module is the canonical low-level Neumann brick for finite convex
combinations of continuous linear endomorphisms close to `-id`.  The immediate
consumer is the branch-native derivative factorization of `chartCmEqnB`; no HCG
geometry belongs in this file.

## Route

- Keep the operator-norm estimate independent of completeness.
- Use the existing `Units.oneSub` Banach-algebra argument for invertibility.
- Preserve `Coordinates.isInvertible_of_norm_id_sub_lt` as a compatibility
  entrypoint backed by this lower theorem rather than maintaining two proofs.

## Status

Focused verification passes for the full module, and the downstream
`LocalDiffeoIFT` compatibility entrypoint also passes after being redirected to
the canonical low-level theorem.  The module is sorry-free.

The local brick is complete (100%):

- `invertible_of_id_sub` supplies the base Neumann criterion;
- `sum_near_neg` proves the weighted operator-norm estimate;
- `sum_near_neg_inv` turns the strict `η < 1` bound into
  `ContinuousLinearMap.IsInvertible`, whose definition contains the required
  `ContinuousLinearEquiv` witness.

No separate equivalence wrapper or inverse-norm theorem was added because the
current `chartCmEqnB` consumer needs only the equivalence witness already stored
in `IsInvertible`.

Honest project accounting: the concrete `CmHessianInput` producer remains
unstated/proved at 0%; its dedicated Hessian/Neumann machinery is roughly 15%
after this generic brick, because the branch-native readout derivative
factorization and quantitative scale choice remain.  Rounded Chapter-4
machinery stays about 82%, and whole-HCG machinery stays about 54%; the
conditional compactness endpoint remains 0% proved.
