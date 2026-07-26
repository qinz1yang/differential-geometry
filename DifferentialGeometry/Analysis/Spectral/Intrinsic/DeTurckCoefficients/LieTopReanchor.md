# LieTopReanchor

## Role

This module is the public, low-regularity bridge from the raw chart Hessian in
the DeTurck Lie principal term to the fixed-background covariant Hessian.

## Current state

- `lieTopTail` records the exact connection tail in the chart-Hessian to
  covariant-Hessian conversion.
- `lieTop_cov_eq_raw` proves that the public DeTurck top coefficient applied to
  the second fixed-background covariant derivative, plus this tail, is exactly
  the raw chart principal expression.
- The identity is algebraic and has no high Sobolev-order hypothesis.

Focused and named-module verification passed without local `sorry`s.  The
remaining work is to absorb and uniformly bound the tail together with the Lie
C0/C1 coefficient fields under C3 data.
