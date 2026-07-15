# Support-independent scalar Hessian bounds

## Goal

Join the invariant scalar Bochner--Green estimate to the actual rank-zero
spectral representative and obtain Laplacian, gradient, and Hessian energy
bounds whose constants do not depend on finite spectral support.

## 2026-07-10

- Added scalar/mixed energy readouts for the realized Laplacian and gradient.
- Added support-independent Laplacian and gradient energy bounds.
- Added the uniform Hessian-energy target with the metric-only constant chosen
  before the spectral vector.
- The proof uses the applied rank-zero pointwise-inner bridge; it does not
  compare whole Hom models and does not add a realization hypothesis.
- The only elaboration repair needed was to give the rank-zero lift equality an
  explicit pointwise type before rewriting inside the tensor inner product.
  This is cheaper and more stable than asking definitional equality to expose
  the bundled section application.
- Focused verification and targeted module verification passed without local
  warnings.

## Intrinsic tensor bounds

- Added `du_energy_le`, identifying the actual canonical one-form `duSec` with
  the already controlled scalar gradient norm pointwise.
- Added `hessSec_energy_le`, rewriting the actual canonical Levi-Civita Hessian
  through `hessSec_normSq` before applying the support-independent chart
  Hessian estimate.
- Both constants are independent of the finite spectral support and its
  cardinality. Focused verification passed without warnings.
- These are complete fixed-metric producers. The geometric moving-Laplacian
  `A2` theorem is still not stated or proved.
