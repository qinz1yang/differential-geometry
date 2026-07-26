# ParametricScalarSmul

## Role

`smul_hs_unif` converts the existing joint-smooth scalar-multiplier covariant-jet estimate into a support-independent spectral Sobolev estimate at every natural order.  The proof stays on `SmoothCcTensor` and sandwiches the multiplier jet bound between `hs_le_jet` and `hsJet_le`.

The estimate is uniform on compact parameter sets and its constant is independent of spectral support.  This is the correct reusable core estimate for the high-scale scalar-potential term in the conjugate-heat Galerkin equation.

## Verified state

The file passes focused verification without `sorry`.

- `smul_hs_unif`: theorem 100%; dedicated core-estimate machinery 100%.
- High-scale scalar-potential continuous linear map: theorem not yet stated (0%); dedicated machinery about 65%.
- Time-continuous high-scale scalar-potential operator path: theorem not yet stated (0%); dedicated machinery about 45%.

## Frontier

This theorem does **not** construct `H^n ->L H^n` and does not prove operator-norm continuity in the parameter.  The next honest producer is the dense-core extension, using the finite-support representation map and the spectral-Sobolev linearity/closed-extension API.  Its construction should wait for the currently active `ccTensorToHs_add` / `ccTensorToHs_smul` producer lane to settle, rather than duplicating that work here.

For the full conjugate-heat route, scalar multiplication is the easier lower-order arm.  The moving Laplacian difference `H^(m+2) -> H^m` and its time regularity remain the larger all-scale API frontier.
