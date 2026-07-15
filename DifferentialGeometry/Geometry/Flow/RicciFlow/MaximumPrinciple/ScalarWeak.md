# Scalar weak maximum principle notes

## 2026-07-09: linear reaction nonnegativity

- `linear_react_nonneg` now closes the negative-region calculation from the
  genuine equation `P u = beta * u` and a uniform upper bound `beta <= C`.
  The earlier book-facing wrapper still accepts that calculation as an input.
- The proof uses the existing exponential rescaling identity.  On the negative
  set, `(beta - C) * u` is nonnegative because both factors are nonpositive.
- The zero-length interval is discharged directly from the initial condition;
  the positive-length case uses uniqueness of derivatives on the closed time
  interval.
- Focused verification passed without `sorry` or warnings.

This completes the generic linear-reaction WMP calculation needed by the
time-reversed conjugate heat equation.  It does not construct a heat solution.
Perelman no-local-collapsing remains 0%; its dedicated analytic machinery is
about 15%, while the whole HCG machinery remains about 45% and its endpoint
theorems remain 0%.
