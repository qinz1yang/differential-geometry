# BundleSmoothEval Notes

## 2026-05-12 heartbeat audit

- Removed the file-level `synthInstance.maxHeartbeats` and `maxHeartbeats`
  bumps.
- The bundle smooth-evaluation file checks at the default heartbeat budget.
- Verification passed.

## 2026-05-10 tensor-field evaluation wrapper

Worked:

- Added `TensorMultilinear.contMDiff_tensor0SField_apply`.
- This is a section-level wrapper around the existing induction theorem
  `TensorMultilinear.contMDiff_section_apply`.
- It states that a smooth `(0,n)` tensor field evaluated on `n` smooth tangent
  sections gives a smooth scalar function.

Why here:

- The theorem is pure multilinear bundle smoothness; it does not depend on
  connections, curvature, or `nabla`.
- Keeping it in `BundleSmoothEval.lean` avoids repeating the model-fiber
  instance plumbing inside later geometry files.

Used by:

- `Tensor0SBundle.tensor0S_eval_covariantDerivative_slot_contMDiff` in
  `DifferentialGeometry/Tensor/RSTensor/NablaOnTensors.lean`.

## 2026-05-10 scalar genericity

Worked:

- Generalized the bundle evaluation continuity/smoothness induction from
  `Real` to a generic scalar field.
- The same induction proves `continuous_section_apply`,
  `contMDiff_section_apply`, `contMDiff_tensor0SField_apply`, and their
  pointwise `ContMDiffAt` analogues over the generic scalar field.

Failed:

- No RCLike or Real-only theorem was needed. The only cleanup was suppressing
  unused-section-variable warnings after the generic variable block grew.

## 2026-05-13 C1 evaluation layer

Worked:

- Added pointwise `C1` versions of the curried-section and multilinear
  bundle-evaluation lemmas.
- These are the minimum regularity needed when one tensor slot is a covariant
  derivative field such as `p |-> nabla_X Y`, which is locally `C1` under a
  locally `C1` connection.
- Verification passed.

Lesson:

- The smooth evaluation theorem is too strong for invariant Ricci-identity
  expansion.  The reusable lower layer is multilinear evaluation at `C1`
  regularity, not a geometry-specific workaround.
