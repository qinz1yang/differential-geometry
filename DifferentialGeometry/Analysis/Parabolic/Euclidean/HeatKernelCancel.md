# HeatKernelCancel

## Status

The complete file passes its focused Lean check without local warnings.  All
listed declarations are proof terms with no `sorry`, `admit`, axiom, or opaque
analytic input.

## Mathematical content

- `integral_heatD2_zero` proves the spatial zero-mean identity for every
  directional second derivative of the Euclidean heat kernel.  It uses
  Mathlib's finite-dimensional Frechet integration-by-parts theorem with the
  constant function and `heatD1`.
- `baseD2Half_int` and `integral_heatD2Half` build the weighted Gaussian
  majorant and prove its exact dilation law.
- `heatScale34_eq` identifies that law with `t^(-3/4)`.
- `heatD2Cancel_int` and `heatD2Cancel_norm` package the reusable
  Banach-valued cancellation operator for global exponent-`1/2` Holder data.
- `heatD2Conv_eq_cancel` uses the zero-mean theorem to identify the ordinary
  second-derivative convolution with that cancellation operator.

The raw `t⁻¹` estimate from `HeatKernelLp` is deliberately not used as a
time-integrable maximal-regularity bound.  The half spatial moment is the
essential gain.

The exact second derivative kernel is globally defined with
`(sqrt t)⁻¹ (sqrt t)⁻¹`.  The half-moment formula uses `t⁻¹` only after proving
the positive-time equality from `sqrt(t)^2 = t`; treating those factors as
definitionally equal was a failed proof route.

## Next boundary

The next Euclidean producers are the sup-norm convolution estimate, the
positive-time heat PDE identity, and the quantitative approximate identity.
After those, the remaining hard Euclidean boundary is differentiation of the
Duhamel space-time integral.  The intrinsic connection Laplacian should later
enter through the existing chart-coordinate expansion APIs.
