# ModelBridge Notes

## 2026-06-14 - Component-eval transparency sweep

Result: focused verification passed after removing the transparency wrapper from
`tensorRSModelAt_coordComponentRSAt`.

The removed wrapper was a pointwise component/model identity. The proof now avoids
the raw `trivializationAt (Tensor0SModel ...)` subproof surface and routes the
input tensor equality through:

- `Tensor0SSpace.constInChart_apply`;
- `ext0S_basis`;
- `basisTensor0S_component`;
- the center tangent-coordinate normalization via
  `TangentBundle.continuousLinearMapAt_trivializationAt_eq_core` and
  `coordChange_self`.

The remaining wrapper on `modelDeriv_eq_coordDerivRSAt` was tested and restored.
Removing it exposes `TensorRSModel` normed-space/topology/fiber-bundle instance
mismatches in the derivative smoothness bridge. That belongs to the
bundle/model-topology workstream, not the component-eval API sweep.
