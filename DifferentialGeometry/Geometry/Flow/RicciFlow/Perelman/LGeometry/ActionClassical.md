# Classical equation bridge for fixed-chart minimizers

## Status

`ActionClassical.lean` now proves the native pointwise bridge
`lChartEuler_iff`. At a regular interior chart point, assuming only
`HasDerivAt u.toFun (q r) r` and pointwise differentiability of `q`, it
identifies the differentiated fixed-chart momentum equation with the second
component of the regularized phase equation at the **global** square-root time
`s = a + r`:

```text
deriv (fun z =>
  chartGramOp S.family p
    (T - (a + z)^2, u.toFun z) (q z)) r
    = lChartForceRep S T a p u q r
  iff
deriv q r = (lPhaseField S T p (a + r) (u.toFun r, q r)).2.
```

The focused check passed without warnings. The theorem has no `sorry`,
`admit`, new class, supplied Euler/acceleration hypothesis, or reference-tree
dependency.

## Proof architecture

The proof remains scalar throughout the moving-fiber calculation.

- `lGramPair_deriv` obtains the derivative of a Gram pairing from
  `lRegInner_deriv`; `lGramPair_shift` transports it from absolute
  square-root time to the local chart parameter without confusing `r` with
  `a + r`.
- The generic producer `chartGram_spatial` turns the spatial `fderiv` term
  into the Christoffel contraction. `lPosRep_apply` reconstructs an arbitrary
  chart direction from the finite basis, and `lForcePair` identifies the Riesz
  force after scalar pairing.
- `lScalPair` uses `chartScalCov_apply`,
  `mfderiv_scalar_eq_chart_fderiv`, and `inner_gradientFun` to identify the
  chart scalar derivative with the intrinsic gradient pairing.
- `lAccelPair` combines that scalar bridge with `lRegAccel_inner`, including
  the native Ricci symmetry sign. Equality of all scalar Gram pairings is
  upgraded to vector equality using `chartGramOp_unit`; no whole bundle,
  tensor-Hom, or moving-fiber object is unfolded or compared.

## Next exact theorem

The immediate consumer is `lChart_min_accel` in a new consumer module. It
should take the `q` and momentum representative supplied by `lChart_mom_c1`
and `lChartVel_c1`, differentiate the momentum identity on `Ioo 0 L`, invoke
`lChartEuler_iff`, and then apply `lPhase_accel` to the shifted global phase

```text
z(s) = (u.toFun (s - a), q (s - a))
```

at `s = a + r`. Applying `lPhase_accel` directly to `(u.toFun,q)` at local
`r` would incorrectly use time `T - r^2` and must not be done.

## Project accounting

`lChartEuler_iff` is complete (100%). The classical-minimizer-to-acceleration
consumer is still unstated (0%), with its dedicated inputs now about 95--98%.
The terminal `exists_lMinimizer` theorem remains 0%, and `redVolume_anti`
remains 0%. Dedicated L-geometry machinery is about 86--90%; generic reused
infrastructure needed by this bridge is 100%. P2 remains below 1%, and the
whole Poincare program remains about 3--5%.
