# LowRegLieOne

## Role

This module is the dimension-three, `C3`-compatible producer for the concrete
order-one DeTurck Lie coefficient.  Its public endpoint is
`lie1_h2_tame`, with the same affine `H3` dependence used by
`ricci1_h2_tame`; `lie1_h2` is the one-parameter compatibility wrapper.

## Mathematical route

- `sharpFlatEndoCc` is split into the inverse-metric difference insertion and
  a fixed parallel-background insertion.  The moving part is integrated with
  the low `H2` jet grid, so this factor uses no third derivative.
- `lieArm1LoweredBgKappa` is identified with `-lc0Kappa`.  The exact
  `kappa_bg` split is applied before estimating: the self-background term is
  controlled by `kappaSelf_h2`, the fixed term is harmless, and `pbLow_h2`
  uses only the lower radius.  Hence the endpoint `H3` size occurs affinely.
- `lieArm1PsiB` is estimated by the dimension-three `H2 x H2 -> H2`
  application estimate.
- The canonical fourteen-piece decomposition of `deTurckLieArm1Coeff` is
  assembled without changing its cancellations or introducing an order-four
  metric jet.

## Current verification state

The source implementation contains no `sorry`, `admit`, or new axiom and is
1023 lines, below the hand-maintained-file limit.  It has received static diff
and dependency/API review only.  A focused Lean check has intentionally not
been run yet because the shared verification slot is owned by another lane.
Until that focused check passes, the exact Lean theorem remains unverified and
the Phase N endpoint remains 0%; this file is machinery, not the endpoint.

## Next check

Run the lock-aware focused check for `LowRegLieOne.lean`.  If elaboration finds
a bridge mismatch, keep the same mathematical route and repair only the
smallest local equality (most likely a definitional reindex/slot-extension
normalization).  After it checks, import `LowRegLieOne` in the order-one RHS
path producer and combine it with `ricci1_h2_tame` through `rhs1_h2_of_aux`.
