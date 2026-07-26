# Defs

## 2026-07-16 base-measure normal form

`wFunctional_base` is the canonical public conversion from the
`perelmanWeightedMeasure` definition of `W` to the scalar-density integral
against the underlying measure.  It requires only nonnegative scale and
measurability of the density.  The theorem was extracted from the former
private `WVariation.w_base_eq`; no geometric or regularity assumption was
added.  Focused verification passed without a new `sorry`.

This theorem is measure-theoretic machinery, not W monotonicity or a W lower
bound.  The base conversion is **100%**; `w_fixed_lower`, no-local-collapsing,
and `ham3_noncollapse` remain theorem-level **0%**.
