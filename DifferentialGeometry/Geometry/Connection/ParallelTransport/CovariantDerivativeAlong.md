# CovariantDerivativeAlong

## Role

This file owns the intrinsic covariant derivative of a dependent tangent
section along a curve and its basic linearity and reparametrization laws.

## 2026-07-23 update

- Added `covDeriv_comp_mul`: covariant differentiation along
  `s ↦ γ (c * s)` of `s ↦ V (c * s)` is `c` times the original covariant
  derivative at `c * t`.
- The proof uses the unconditional model-space derivative identity
  `deriv_comp_mul_left`, so it does not add artificial differentiability
  hypotheses.
- Focused verification passed, and the current artifact is successfully
  consumed by the focused-green radial-Laplacian compatibility theorem.

## Accounting

- Multiplicative reparametrization helper: theorem 100%.
- This is a small generic API brick; it does not by itself prove the raw radial
  Laplacian identity or advance the unconditional HCG endpoint theorem.
