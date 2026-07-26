# ConjCriticalTame

## Role

`scalar_crit_tame` is the solution-specific finite-core closure needed by the
scalar non-autonomous Galerkin energy hierarchy.  It combines the genuine
moving-minus-frozen scalar Laplacian with the time-reversed conjugate-heat
potential `-R` on one common terminal-time interval.

The theorem chooses the interval and the full order-indexed lower-constant
family before the time, Sobolev order, finite spectral set, and finite-support
vector.  The A2 top coefficient is `5/3`; the A1 coefficient is `1/4`; hence
the combined coefficient is `23/12 < 2` and leaves coercivity `1/12`.

## Current state

The solution-specific theorem and its full dependency chain now pass focused
verification.  Its one-interval generic A2 producer `cc_a2_unif` is verified
in the lower Garding layer; the A1 arm uses `cc_a1_unif` and `conjCoeff_rev`.
No consumer assumption or chart-local-constancy hypothesis was added.

The final local repairs were elaboration-only: the scalar spectral index was
qualified to the `TensorHeatEquation` alias, the Sobolev-order binder was
annotated as `ℕ`, and the local pairing `let` was unfolded with `simp only`
before linearity.  The mathematical statement and `23/12` coefficient did not
change.

The scalar finite-dimensional Galerkin ODE producer now exists separately.
The active frontier is verification of its uniform energy bound and the
subsequence/limit construction, followed by identification with a classical
conjugate-heat solution.

## Honest progress

- `scalar_crit_tame`: theorem and dedicated machinery 100% verified.
- `scalar_gal_exists` and `scalarGalPert_fin`: theorem-level 100% verified.
- `scalar_gal_bound`: theorem-level 0% pending its own verification; dedicated
  machinery is approximately 95%.
- `scalar_gal_subseq`: theorem-level 0% pending its own verification; dedicated
  machinery is approximately 95%.
- `heatpot_of_maxreg`: not started as a theorem (0%); dedicated reusable
  machinery is approximately 35%.
- Classical moving conjugate heat: theorem-level 0%; dedicated machinery is
  approximately 80%.
- Perelman no-local-collapsing and `ham3_noncollapse`: theorem-level 0%;
  dedicated analytic machinery is approximately 44%.
- Whole HCG compactness machinery is approximately 54%; endpoint theorems
  remain 0%.
