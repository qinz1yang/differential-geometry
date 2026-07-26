# GalerkinCompactness

## Scope

This lower intrinsic-spectral module contains reusable scalar compactness
producers for the Galerkin-limit route.  It deliberately does not construct a
Galerkin subsequence or import Ricci-flow/HCG endpoint modules.

## Producers

- `fatou_sq_mass` is the rank- and geometry-independent finite-coordinate
  Fatou estimate.  It was moved from the proof shape of
  `fatou_weighted_sq_mass_le` without adding assumptions.
- `right_lipschitz` turns continuity on `Icc a b`, right-within derivatives on
  `Ico a b`, and one uniform derivative bound into `LipschitzOnWith` on the
  closed interval.  The proof applies Mathlib's one-sided mean-value estimate
  to the ordered interval between each pair of points.
- `galerkin_subseq` packages each coordinate curve as a bounded continuous
  function on `Icc 0 τ`, applies Arzelà--Ascoli modewise, takes the compact
  countable product of the resulting closures, and extracts one strict
  subsequence.  The coordinate limits are extended to globally continuous
  real-time curves with `IccExtend` while convergence is asserted only on the
  original compact interval.

## Verification

Focused verification passed without errors or warnings for all three
producers.  The targeted module refresh also passed.

The proof-normal-form details that mattered were:

- the bounded-continuous-function arrow notation needs its scoped notation;
- the two binders in the restricted uniform-convergence function need separate
  type annotations, so the subsequence index stays a natural number;
- the final restriction/extension equality is cheapest as one function
  extensionality step followed by `IccExtend_val`.

## Honest status

`fatou_sq_mass`, `right_lipschitz`, and `galerkin_subseq` are each
theorem-complete (100%); this three-producer file is complete (100%).  The
entropy-facing `scalar_gal_subseq` remains unstated/unproved (0%), while its
dedicated machinery is approximately 80%.  The classical moving
conjugate-heat endpoint remains 0% (dedicated machinery approximately 78%); the
Perelman noncollapsing endpoint remains 0% (dedicated analytic machinery
approximately 44%); whole HCG machinery remains approximately 54% with its
endpoint theorems still 0%.
