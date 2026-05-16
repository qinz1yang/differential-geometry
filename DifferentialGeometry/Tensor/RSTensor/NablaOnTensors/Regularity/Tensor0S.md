# Tensor0S.lean Notes

## Goal

Expose a public `(0,s)` tensorial covariant-derivative rule matching Definition
14.5, so later Ricci-identity arguments can use the invariant moving-slot
formula instead of reopening the coordinate/model construction.

## Result

- Added `nabla0SFun_eval_smooth_slots`.
- The theorem states that evaluating `nabla0SFun` on smooth moving vector-field
  slots equals the exterior derivative of the scalar evaluation minus the sum
  of covariant-slot correction terms.
- The proof packages smoothness of the tensor field and the moving slots, then
  delegates the actual algebra to the existing raw theorem
  `nabla0SFun_eval_coordFrame_moving_raw`.

## Failed

- Tried to silence the new unused-section-variable warning with a local `omit`,
  but Lean rejected it because a generated section variable is still referenced
  in the proof term. The theorem was left in the compiling form rather than
  introducing a broader variable refactor.
- Follow-up: the file now disables `linter.unusedSectionVars` once in the
  header. This matches the existing file shape better than local `omit`
  annotations for each theorem.

## Verification

- Focused verification passed.
- Targeted downstream builds passed.

## Lessons

- The right public theorem is not another coordinate component lemma. The raw
  coordinate/model proof should stay as implementation detail, while
  `nabla0SFun_eval_smooth_slots` is the tensorial API matching Definition 14.5.
- Smooth moving-slot hypotheses are enough to feed the raw theorem: they give
  differentiability of the scalar pairing, chart-model differentiability of
  each slot, and differentiability of coordinate components.

## 2026-05-13 C1 moving slots

Worked:

- Added `nabla0SFun_eval_C1_slots`, the Definition 14.5 rule for moving slots
  that are only locally `C1`.
- Added C1 chart-model helpers for tangent-field representatives and their
  coordinate components.
- Verification passed.

Remaining risk:

- This closes the regularity bridge needed for the invariant tensor Ricci
  identity, but it does not itself perform the commutator expansion.  The
  remaining frontier is now in `Tensor/RicciIdentity.lean`.

## 2026-05-13 C1 tensor evaluation extracted

Worked:

- Extracted the tensor-evaluation regularity used by `nabla0SFun_eval_C1_slots`
  into public helpers:
  `tensor0SField_eval_smooth_slots_contMDiffAt`,
  `tensor0SField_eval_C1_slots_contMDiffAt_one`, and
  `tensor0SField_eval_C1_slots_mdiffAt`.
- Refactored `nabla0SFun_eval_C1_slots` to consume the new helper instead of
  rebuilding the scalar-pairing differentiability proof inline.
- Verification passed.

Lesson:

- The C1 moving-slot regularity is reusable outside the covariant derivative
  formula.  Keeping it in the tensor/nabla regularity layer lets Ricci identity
  proofs differentiate scalar evaluations without reopening bundle topology
  arguments.

## 2026-05-14 tensor local-frame extraction

Worked:

- Moved non-nabla tensor smoothness helpers to
  `Tensor/RSTensor/LocalFrameRegularity.lean`.
- This file now keeps the connection-specific pieces: covariant derivative of
  chart-constant tangent slots, local `(0,s)` covariant derivative correction
  regularity, moving-slot derivation formulas, and `nabla0S_reg`.

Verification passed.

Lesson:

- Smooth evaluation and chart-constant tensor-section regularity are lower
  tensor-bundle facts.  The `(0,s)` nabla file should start where connection
  correction terms enter.
