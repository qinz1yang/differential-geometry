# RedVolumeUniform

## Role

This module is the compact finite-cover assembly between the verified joint
parameter lower semicontinuity of reduced volume and the smooth noncollapsing
endpoint.  It does not assume uniform convergence as an input.

## Public statement

`redVolume_unif_low` assumes a compact terminal-time interval `[a,b]`, a
positive backward radius `rho`, and the pointwise weakest regular-slab input

```text
forall T in [a,b], [T-rho,T] is regular.
```

It produces one `tau0` with `0 < tau0 < rho` such that, simultaneously for
every `T` in `[a,b]`, every basepoint `x`, and every `0 < tau <= tau0`,

```text
1/2 < redVolume S T x tau.
```

The interval nonemptiness hypothesis `a <= b` is used only to make the finite
subcover nonempty and hence to take its positive finite infimum.

## Source route

1. At each `(T,x)`, `redVolume_zero_lim` selects a positive
   `tau_(T,x) < rho` where reduced volume is strictly above one half.
2. `redVolume_lsc` turns that strict bound at the selected fixed time into an
   actual neighborhood of `(T,x)` in the joint parameter space.
3. Compactness of `[a,b] x M` and `IsCompact.elim_nhds_subcover'` select
   finitely many such neighborhoods.  This API consumes neighborhoods
   directly, so no separate openness upgrade is needed.
4. `Finset.inf'` of the finitely many positive selected times is a positive
   common floor `tau0`.
5. `redVolume_anti` first transfers the neighborhood bound from each selected
   time down to `tau0`, and then from `tau0` down to every
   `0 < tau <= tau0`.

This is a genuine compactness producer.  Its hypotheses contain neither a
uniform small-time limit nor a uniform reduced-volume lower bound.

## Verification

The complete module passes a warning-free focused Lean check, and its named
module refresh completed successfully.  The selected times are indexed by the
compact-set subtype itself, so they do not depend on membership proofs.  The
finite subcover, its nonemptiness, the positive finite infimum, and both
antitonicity transfers all elaborate without an additional topology or
measure-theory assumption.  The refresh exposed only pre-existing warnings in
upstream L-geometry modules, not in this module.

## Progress accounting

- `redVolume_unif_low`: source and verified theorem 100%.
- Dedicated compact finite-cover and uniform-floor machinery: source and
  verified machinery 100%.
- `redVolume_lsc`: source and verified theorem 100%.
- `smooth_nlc`: theorem 0%; its dedicated reduced-volume-to-volume comparison
  machinery remains at the next frontier.
- Whole Perelman L-geometry program, including the later L8--L9 layers:
  approximately 45%.  The compact fixed-manifold L0--L7 machinery is tracked
  separately at approximately 99%.  P2 remains below 1%; the final Poincare
  endpoint theorem remains 0%, while full-program infrastructure is
  approximately 15--25%.

## Next target

The next mathematical frontier is the reduced-volume-to-ball-volume comparison
needed by the downstream `smooth_nlc` endpoint.
