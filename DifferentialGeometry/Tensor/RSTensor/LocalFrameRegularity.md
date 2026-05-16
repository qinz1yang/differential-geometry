# LocalFrameRegularity notes

## 2026-05-14: Extracted tensor local-frame regularity

Worked:

- Moved tensor-section smoothness helpers out of the nabla regularity file when
  they did not depend on covariant differentiation.
- The new layer owns chart-constant `(0,s)` tensor section smoothness, model
  representative differentiability for `(0,s)` sections, smooth mixed-tensor
  evaluation, and chart-constant tangent-slot evaluation.
- `NablaOnTensors/Regularity/Tensor0S.lean` and `TensorRS.lean` now consume
  these helpers while keeping the actual nabla derivation and connection
  regularity proofs.

Verification passed.

Lesson:

- Tensor local-frame smoothness is a reusable bundle/tensor fact.  The nabla
  layer should only add derivative formulas and connection-specific correction
  terms.
