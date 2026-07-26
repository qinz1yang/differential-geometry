# HeatKernelSPD

## Purpose

This file supplies the exact frozen-principal-coordinate reduction needed by
the low-regularity parabolic route.  For a real positive-definite matrix `A`,
`spdSqrtEquiv A hA` is induced by Mathlib's canonical positive square root
`CFC.sqrt A`.

## Source-level facts implemented

- applying `spdSqrtEquiv` twice is the continuous linear action of `A`;
- the equivalence is self-adjoint;
- `‖L x‖² = ⟪x, A x⟫`;
- an upper quadratic-form bound `⟪x, A x⟫ ≤ ellMax ‖x‖²` gives
  `‖L‖ ≤ √ellMax`;
- a lower bound `ellMin ‖x‖² ≤ ⟪x, A x⟫`, with `ellMin > 0`, gives
  `‖L⁻¹‖ ≤ (√ellMin)⁻¹`.

The construction exposes no eigenbasis and introduces no class or instance.

## Verification state

Source-only implementation.  A concurrent named build owns the shared Lean
build lane, so this file has not yet received its required focused check.  The
next step is to check this file, then instantiate it for the frozen chart
inverse-Gram matrix using `IsLowRegCoeff.elliptic`.
