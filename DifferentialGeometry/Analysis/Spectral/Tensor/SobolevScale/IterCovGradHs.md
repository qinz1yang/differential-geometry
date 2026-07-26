# IterCovGradHs

## Purpose

This module completes fixed-background iterated covariant differentiation as a
bounded map

```text
H^(k+j)(T^0_s M) -> H^k(T^0_(s+j) M).
```

It is the spatial-order bridge used by the scalar nonautonomous Laplacian
factorization. The construction stays at the canonical dense smooth-tensor
embedding and does not add a coordinate or realization wrapper.

## Verified result

Focused verification and the targeted module build pass without `sorry`.

- `iterCovGradHs` is the completed continuous linear map obtained from
  `ccGrad_le` and `LinearMap.extendOfNorm`.
- `iterCovGradHs_core` proves agreement with `iteratedCovGrad` on every smooth
  compact tensor embedded by `ccTensorToHs`.

No new geometric assumptions or topology instances were introduced.

## Frontier

This producer is **100%** complete. Its immediate consumer is
`ScalarNonautTime.lapDiffHs_decomp`, which combines the order-two and order-one
maps with the completed coefficient actions.

Project accounting remains separate: the original minimal `A2` estimate and
its all-scale completed form are **100%**; the Perelman noncollapsing endpoint
itself remains **0%**.
