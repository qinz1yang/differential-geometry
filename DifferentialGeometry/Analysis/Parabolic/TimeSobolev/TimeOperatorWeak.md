# Weak limits of time operators

## Purpose

`timeOp_weak_lim` records the stable product limit used by chart-local direct
methods when a concrete `NNReal` error rate has already been chosen.
`timeOp_weak_unif` gives the rate-free form consumed by geometric uniform
convergence theorems: for every positive real tolerance, the coefficient error
is eventually bounded by that tolerance almost everywhere. Each approximating
coefficient retains its own essential bound. No separate input bound is required
for the weakly convergent sequence: Banach--Steinhaus supplies it from the scalar
test convergence.

Both proofs use the existing `timeOp` realization and norm estimate. They split
the product into a coefficient-error term, which converges strongly to zero,
and a fixed-operator term, whose weak convergence follows by testing against
the adjoint. The rate-free proof chooses a tolerance only inside the neighborhood
argument; it does not manufacture a persistent error sequence.

## Verification

Focused verification passes without warnings or placeholders.
