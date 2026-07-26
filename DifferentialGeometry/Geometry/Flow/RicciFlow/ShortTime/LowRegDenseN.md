# LowRegDenseN

## 2026-07-19

The first low-regularity dense-extension bridge is now written:

- `smoothHs_inj` specializes the generic injectivity of the smooth spectral
  embedding to the rank-two scale used by Ricci--DeTurck;
- `smoothN_wd` shows that equal smooth spectral representatives give the same
  `deTurckSmoothN`, with no supercritical-order hypothesis.  Equality of the
  spectral representatives first gives equality of the smooth tensors, and
  the two metric realizations are then equal by their common inner-product
  formula.

This is a real simplification of the dimension-three `Dense.extend` route, but
it is not yet the Lipschitz or mixed estimate.  Focused verification is
pending while the shared long-path `.olean` dependency is rebuilt exclusively
by the product-estimate lane.  Both exact analytic endpoint theorems remain
unproved.
