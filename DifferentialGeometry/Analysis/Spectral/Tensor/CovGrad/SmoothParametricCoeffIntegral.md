# SmoothParametricCoeffIntegral

## Role

This module supplies generic integration and differentiation tools for smooth
parameter-dependent tensor coefficients.

## 2026-07-16 coefficient application integrability

`coeffApp_integrable` proves interval integrability after applying a jointly
smooth coefficient field to a fixed tensor and evaluating through `unitModel`.
It is generic in the output arity and in the ambient parameter set containing
`uIcc 0 1`, replacing a private three-arm-specific helper.

Focused verification and the named module build pass without a local `sorry`.
This helper is complete (100%); the mixed `H3 -> H1` endpoint remains
theorem-level 0%.
