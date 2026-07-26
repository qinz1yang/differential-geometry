# Potential

## Verified producer

`Potential.lean` defines `perelmanPotential` directly from a positive scalar
density and proves:

- `density_potential`: for `tau > 0` and pointwise positive `u`, substituting
  the reconstructed potential into `perelmanDensity` returns `u` exactly;
- `weighted_potential`: the corresponding Perelman weighted measure is exactly
  `mu.withDensity (ENNReal.ofReal ∘ u)`.

The proof is entirely scalar.  Positivity of `tau` is used only to prove that
the density prefactor is positive, so the logarithm and cancellation are
legitimate.  No flow, regularity, chart, or nonemptiness assumption was added.

Focused verification passed without a local `sorry`.

## Honest frontier

These two bridge theorems are complete (100%).  They are dedicated W-entropy
machinery, not the W-monotonicity or no-local-collapsing theorem itself.

- Reverse-time interval W antitonicity: checked in `WVariation.lean` (100%).
- Perelman no-local-collapsing endpoint: not yet stated/proved in Lean (0%).

The remaining work separates into three genuine classes:

1. potential evolution and regularity: transfer the positive conjugate-heat
   solution through `-log` and prove the spatial/time derivative identities;
2. geometric variation: supply the real moving-metric derivative of
   `|grad f|^2` (and the compatible scalar/Hessian inputs) to the existing first
   variation framework;
3. entropy completion and application: prove the weighted integration-by-parts
   and square-dissipation identity, then the localized analytic estimates that
   turn W monotonicity into noncollapsing.

## 2026-07-16 geometric reuse

`prefactor_pos` is now public so geometric consumers can reuse the canonical
positive-scale fact instead of unfolding the rpow prefactor.  The new sibling
module `PotentialGeometry.lean` proves `potential_grad`,
`potential_grad_sq`, `potential_square`, and `square_pot_energy`.  These give
the reusable identities `grad f = -u^{-1} grad u` and, for `u = v^2`,
`u |grad f|^2 = 4 |grad v|^2`.  Focused verification passed without a new
`sorry`.

These scalar/pointwise bridges are **100%** and feed the fixed-metric W
normal form.  Interval W antitonicity is separately **100%**;
`w_fixed_lower`, no-local-collapsing, and `ham3_noncollapse` remain
theorem-level **0%**.

## 2026-07-16 prefactor logarithm

`log_prefactor` is checked.  It exposes the exact logarithm of Perelman's
positive density prefactor and is the scalar cancellation used by
`w_fixed_lower`.  The theorem is **100%** and adds no new assumption.

The downstream `w_fixed_lower` and its density-form adapter are now checked.
This does not complete the intrinsic cutoff, `NoLocalCollapsing`, or
`ham3_noncollapse`; those endpoint theorems remain **0%**.
