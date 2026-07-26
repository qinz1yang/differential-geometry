# Fine principal freezing error

## Source facts

- `fineOscRadius` is selected from the fixed chart-buffer radius, the
  family-uniform first-derivative bound for inverse Gram entries, and the
  uniform maximal-regularity Hessian constant `K₂`.  It has no dependence on
  the family member or on the later time horizon.
- `fineOscRadius_pos`, `fineOscRadius_le`, `fineOsc_coeff_lt`, and
  `fineOsc_mul_lt` prove that this radius is positive, stays inside the
  buffer, makes the entry oscillation small, and makes the full coefficient
  times Hessian-solver constant strictly less than `1/4`.
- `invGramOscBound` retains the sharper coefficient constant
  `L * fineOscRadius r₀ L K₂`; `invGramOscQuarter` records that it is strictly
  below one quarter.
- `principalOsc_bound`, `principalOsc_const`, and `principalOscQuarter` turn
  entrywise oscillation into a norm estimate for the complete finite
  second-order arm.
- `invGramB2Bound` retains the strict uniform multiplier constant for the
  actual inverse-Gram principal arm, while `invGramB2Quarter` supplies the
  convenient coarse quarter estimate.
- `b2Error_quarter` combines the fine multiplier bound with the complete
  frozen-solver Hessian map bound and proves the strict quarter estimate for
  the concrete operator `C₂ ∘ D₂ ∘ H ∘ E`.  It does not assume `‖B₂‖` as a
  separate hypothesis.

This is deliberately the spatial principal-error estimate.  Its operator
lift is now explicit, but the concrete W3p coefficient multiplier and
frozen-heat Hessian maps still have to be constructed.  Cutoff and transition
commutators are first/zero order and are handled separately by the small-time
`B₁₀` estimate.

## Verification state

Source implementation completed on 2026-07-19.  Lean verification is pending
because the shared named build/export lane currently owns the build lock.  No
Lean process was started for this file, and no `sorry`, `admit`, axiom, opaque
placeholder, or metric-dependent shrink was introduced.

Endpoint accounting remains unchanged until checked downstream assembly:
`ricci_flow_unif_existence` is 0%; the fine-principal-error machinery is
source-complete but unverified.
