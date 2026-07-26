# Gradient chart bridge

## Current state

- `gradient_eq_gradFun` records that the connection-layer `gradientFun` and the
  chart/local `gradFun` are definitionally the same metric dual of `df`.
- The theorem is pointwise, has the weakest assumptions required by the two
  definitions, and its proof is `rfl`.
- Focused verification passed.  The file's pre-existing unused-section-variable
  warnings remain unrelated to this bridge.

## Role in HCG

This is a compatibility brick for rewriting a locally smooth gradient field
before taking its Levi-Civita covariant derivative.  It is supporting machinery
only; it does not prove the local Hessian identity or either HCG endpoint
producer.
# Gradient chart bridge

`gradient_eq_gradFun` records the pointwise definitional compatibility between
the connection-layer gradient and the canonical chart gradient.  Focused
verification passed.  Local scalar-germ and Hessian localization live in the
Hessian bridge rather than creating a second gradient hierarchy here.

## 2026-07-17 finite-sum bridge

`gradFun_finset` makes pointwise gradient additivity available for finite sums
with an arbitrary-universe index type.  The first attempt used Mathlib's
`MDifferentiableAt.sum`, whose index is universe-zero in the live version and
therefore failed for `Finset M`.  The checked proof instead establishes
finite-sum differentiability by induction and then iterates `gradFun_add`.

The temporary `omit [FiniteDimensional ℝ E]` linter cleanup was invalid because
the surrounding section instances reference it; it was removed.  Focused
verification and the exact targeted module refresh passed.  Pre-existing
unused-section-variable warnings elsewhere in the file are unchanged.

## 2026-07-17 subtraction bridge

`gradFun_neg` and `gradFun_sub` now live beside `gradFun_add` and
`gradFun_const_smul`, their canonical low-level home. This avoids making the
Perelman cutoff layer import the high-level polarised Bochner development just
to linearize a gradient error. Both statements are fully pointwise and add no
regularity or geometric assumptions. Focused verification and the targeted
module refresh passed; the file's older unused-section-variable warnings are
unchanged.
