# TimeQuadratic

## Scope and status

This file supplies the compact weak-lower-semicontinuity brick for time-dependent quadratic
forms on `timeL2`. The requested adapter is complete and focused verification passes without
warnings or placeholders.

- `timeQuad` is the quadratic form `⟨timeOp A u, u⟩`.
- `timeQuad_int` proves the pointwise density is interval integrable directly from the existing
  operator-family measurability and essential bound plus `u : timeL2`; consumers need not assume
  integrability separately.
- `timeQuad_eq_integral` identifies this Hilbert-space quadratic form, for `0 ≤ T`, with
  the interval integral of `inner (A t (u t)) (u t)` on `[0,T]`.
- `timeQuad_nonneg` assumes only a.e. positive semidefiniteness; self-adjointness is not needed
  for this conclusion.
- `timeQuad_convex` assumes a.e. self-adjointness and positive semidefiniteness.
- `timeQuad_weak_lsc` gives `LowerSemicontinuous` after transporting the domain to
  `WeakSpace ℝ (timeL2 X T)`.

This local stage is 100% complete. Any later compactness or minimizer theorem that consumes this
API remains a separate endpoint and is 0% complete in this file; no such endpoint is claimed here.

## Native API route

The implementation reuses `timeOp` and `timeOp_apply_ae` from `TimeOperator.lean` and the native
Bochner `L²` inner-product formula `L2.inner_def`. Pointwise a.e. self-adjointness is integrated to
symmetry of `timeOp`, while pointwise a.e. positive semidefiniteness gives nonnegativity of its
quadratic form.

The interval-integral bridge needs no extra measurability or integrability hypotheses:
`timeQuad_int` reuses `L2.integrable_inner` for `timeOp A u` and `u`, then transfers along
`timeOp_apply_ae`. The assumption `0 ≤ T` only identifies the restricted `[0,T]` measure with
the forward interval.

The convexity proof is a private Hilbert-space quadratic identity, so no generic public wrapper is
left behind. For weak lower semicontinuity, norm-continuity and convexity make every sublevel set
norm-closed and convex. `Convex.toWeakSpace_closure` then shows its image in `WeakSpace` is closed,
and `lowerSemicontinuous_iff_isClosed_preimage` supplies the stable public statement.

## Boundary

No square-root operator, spectral theorem, path-space foundation, new class, or stronger consumer
assumption is introduced. The neighboring `TimeOperator.lean`, `TimeH1Compact.lean`, and
Arzelà–Ascoli files were not edited.
