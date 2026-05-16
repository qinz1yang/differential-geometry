# NablaOnTensors RawDefs Notes

## 2026-05-11 RS raw-definition alignment

Worked:

- `mcovariantDeriv_tensorRSWithin` now mirrors the `(0,s)` raw definition:
  it forms `T'` with `tensorRSModelInChart` and transports the model result back
  through the mixed tensor-bundle `trivializationAt`.
- This removes the older pointwise use of `tensorRSSpace_continuousLinearEquiv`
  inside the raw RS derivative.

Why:

- The previous pointwise model equivalence was not aligned with the fixed
  tensor-bundle coordinates used by `nablaRS_reg`.
- Aligning the raw definition makes the self-chart scalar derivative bridge
  look like the closed `(0,s)` proof, without introducing a fixed-chart
  naturality theorem.

Remaining:

- `nablaRS_reg` is still proved in `Regularity.lean` and still has one scalar
  smoothness frontier.

## 2026-05-11 extraction cleanup

Completed:

- Split raw definitions into:
  - `RawDefs/MCovariant.lean` for model-to-bundle raw covariant derivative
    constructors;
  - `RawDefs/Bundled.lean` for `nabla0SFun`, `nablaRSFun`, regularity
    predicates, and bundled APIs.
- Kept `RawDefs.lean` as a compatibility wrapper.

Verified:

- Verification passed.
## 2026-05-11: Smooth default

- Lowered the raw model-centered default regularity parameter from `top` to `infty`. The definitions remain generic in `n`; the default no longer injects analytic regularity into omitted arguments.
- `nabla0SFun` and `nablaRSFun` now expose smooth inputs and fields in their public bundled layer.
- Verification passed.
