# PartialDerivIteratedFDerivOrderBridge

## 2026-07-14 order-one through order-three bridge

`partial_eq_iter1`, `partial2_eq_iter2`, and `partial3_eq_iter3` identify nested
coordinate partial derivatives with the corresponding evaluations of
`iteratedFDeriv` at smooth points.  These lemmas let intrinsic compactness
bounds feed explicit chart coefficient formulas without unfolding derivative
implementations downstream.

Focused and targeted verification passed.  The bridge is reusable calculus
machinery; it is not an existence result.
