# WkpForcingBridge

## Source-only status

This file is a deliberately small bridge from the theorem-valued chart
Sobolev completeness result to a time-forcing Banach space.  No Lean/Lake
check was run in this lane because a different named build owns verification.

Proved in source:

- `WkpTimeL2` is the raw Mathlib Bochner `L²` space with values in
  `WkpChartQuot`.
- `wkpTime_complete` locally installs `wkpQuot_complete` and returns the
  induced `CompleteSpace (WkpTimeL2 ...)` structure.
- `wkpTime_fixed` applies `ContractingWith.fixedPoint` and proves existence
  and uniqueness of a fixed point for any genuine contraction on this
  carrier.

No global `CompleteSpace` instance, class, or notation is introduced.

## Audit result for the Ricci--DeTurck fixed-point route

`TensorMaximalRegularity/PartialForcingFixedPoint.lean` does not use
`WkpChart`, `WkpChartQuot`, or `WkpChartL2Quot`.  Its contraction acts on

```lean
timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T
```

and its state ball is a subtype of

```lean
tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)
```

`tensorHs` already has a global `CompleteSpace` instance (through its
isometric spectral realization), and Mathlib supplies completeness of the
outer `Lp` carrier.  Hence `partial_sol_const` already has the Banach
fixed-point interface it consumes.  The new chart completeness theorem is not
a missing dependency of that spectral proof.

`AtlasNorm/L2.lean` defines the same scalar membership subtype with a different
Hilbert atlas norm and equips `WkpChartL2Quot` with an inner-product-space
instance, but it explicitly stops before completeness.  There is currently no
proved norm equivalence between its square-sum norm and the generic
sum-of-chart-norms used by `WkpChartQuot`; `wkpQuot_complete` therefore cannot
be installed as a `CompleteSpace WkpChartL2Quot` by definitional equality.

## What this bridge does not prove

The separation quotient has no canonical pointwise evaluation map.  A
pointwise/Nemytskii operation descends only after proving that it respects
zero chart-Sobolev distance (equivalently the chart-a.e. relation).  Choosing
an arbitrary representative would not preserve the required Lipschitz or PDE
meaning and is not used here.

A chart-space replacement for the existing spectral maximal-regularity route
would need, before any fixed-point application:

1. completeness of the tensor-valued chart Sobolev quotient (the raw genuine
   tensor carrier, finite component norm, and a.e. quotient now exist
   source-only in `Sobolev/Tensor/ChartWkp.lean`, but their chart-limit
   compatibility/assembly theorem is still missing);
2. quotient-safe realization of the Ricci--DeTurck nonlinearity;
3. a linear parabolic solution operator with the two-spatial-derivative gain
   and trace/time-derivative identities already provided spectrally by
   `maxRegDuhamelSolField` and `maxRegDuhamelMap`.

Consequently the current uniform-existence lane is not blocked merely on a
missing `CompleteSpace` or Banach fixed-point wrapper.  It also cannot close
the exact endpoint solely through the existing spectral `partial_sol_const`
route: `ricci_flow_unif_existence` is dimension-general and assumes only
uniform `C³` metric control, whereas the present `H³ -> H¹` three-arm tame
estimate obtains the required Sobolev algebra/small-coefficient bounds only in
dimension three.  In higher dimensions, `C³` does not supply a uniformly
bounded spectral `H^s` algebra at the larger `s` demanded by dimension.

Thus the fixed-`g₀` spectral lane is a genuine three-dimensional
specialization, not a proof route for the public theorem as stated.  The
dimension-general route must proceed through a tensor-valued chart
`W^{k,p}` quotient (with an exponent chosen relative to dimension),
quotient-safe Ricci--DeTurck nonlinearities, and maximal-`L^p` regularity on
that carrier, followed by same-horizon realization and smoothing.
`ricci_flow_unif_existence` remains unproved until those producers and the
uniform family assembly are complete.

## Honest progress

- Local chart-forcing completeness/fixed-point plumbing: 95% source-complete,
  focused verification pending.
- Genuine tensor `W^{k,p}` carrier, finite norm, and a.e. quotient: 90%
  source-complete in `Sobolev/Tensor/ChartWkp.lean`; 0% Lean-verified in this
  lane, and quotient completeness remains 0%.
- Chart-valued Ricci--DeTurck maximal regularity: 0%; the necessary tensor
  completeness and quotient-safe PDE operators do not yet exist.
- Fixed-background spectral `H³ -> H¹` lane: useful only for the
  three-dimensional specialization; it does not discharge the
  dimension-general endpoint.
- Exact endpoint `ricci_flow_unif_existence`: 0% in this file.
