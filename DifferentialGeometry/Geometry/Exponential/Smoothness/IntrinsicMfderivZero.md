# IntrinsicMfderivZero.lean

## 2026-07-23 — component-local zero derivative

`mfderiv_expMapIntrinsic_at_zero` now explicitly omits `ConnectedSpace M`.
Its proof already uses only the local small-velocity agreement with the
chart-fixed exponential map and the derivative of that local germ, so no
connectedness argument was removed or replaced.

Focused verification passed with the weaker signature. The exported artifact
still needs its coordinated narrow refresh before downstream files can observe
the change.
