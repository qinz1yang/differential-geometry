# ScalarPotentialPairing

## Role

This file closes the finite-spectral lower-order scalar-potential pairing on a
compact parameter set.  It consumes the joint scalar multiplier estimate from
`ParametricPairing` and the finite spectral pairing identity; it introduces no
new convergence or geometric assumptions.

## Current state

`cc_a1_unif` is stated with a support-independent and parameter-independent
lower constant and the fixed top coefficient `1/4`.  Focused verification and
the named-module refresh now pass after the parametric scalar-multiplier imports
were refreshed.

The theorem is generic coefficient machinery.  The conjugate-heat
specialization still has to compose `conjCoeff_joint` with the spacetime-factor
swap and then combine this `1/4` estimate with the A2 `5/3` estimate, giving the
strict total coefficient `23/12 < 2`.

## Honest progress

- `cc_a1_unif`: theorem and dedicated machinery complete (100%), verified.
- Conjugate-heat A1 specialization: not yet stated or proved (0%).
- Full time-uniform A1+A2 finite Galerkin closure: not yet stated or proved
  (0%).
- Perelman no-local-collapsing endpoint: not yet stated or proved (0%); its
  dedicated analytic machinery is approximately 41%.
- Whole HCG compactness machinery is approximately 53%; endpoint theorems
  remain 0%.
