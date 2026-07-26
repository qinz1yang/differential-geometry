# HeatKernelLp

## Current boundary

The file source-defines the Euclidean heat operator as a Banach-valued average
of translations on `L^p`, together with:

- scalar and continuous-linear-map-valued `L^1 -> L^p` kernel bounds;
- a normalized finite-dimensional Gaussian heat kernel;
- explicit first and second spatial derivative kernels;
- their Fréchet derivative identities and the expected `t^(-1/2)` and
  `t^(-1)` `L^1` estimates;
- the corresponding `L^p` contraction and smoothing operators.

The complete file now passes its focused Lean check without local warnings.  It
contains no `sorry`, `admit`, axiom, opaque declaration, or heartbeat override.

Two implementation corrections were essential.  A finite-dimensional normed
space still needs its explicit Borel measurable structure at the integration
API boundary.  Also the globally defined second derivative kernel must carry
the exact factor `(sqrt t)⁻¹ * (sqrt t)⁻¹`; replacing it definitionally by
`t⁻¹` is justified only under the positive-time hypothesis.  The positive-time
integral and `L^p` estimates prove that conversion rather than assuming it.

## Important non-result

The estimate `||D²H_t||_{L¹} <= C/t` is not time-integrable at zero.  It does
not by itself prove Duhamel maximal regularity, and this file makes no such
claim.  A true `L^p`-in-time route would still require a Calderón–Zygmund or
equivalent maximal-regularity theorem and a proved exchange between the
Banach-valued convolution and weak spatial derivatives.

The selected dimension-generic existence route is instead parabolic Hölder:
spatial zero-mean cancellation for `D²H_t`, plus spatial Hölder and temporal
Hölder moduli, produces the integrable singular powers needed by Schauder
estimates.  `HeatKernelLp.lean` is therefore paused at this honest boundary.

## Status

Analytic machinery stated in this file: 100% proved and focused-verified.  It is
not an endpoint producer.  The Euclidean Schauder/Duhamel chain remains
incomplete, and both exact continuation theorems remain 0% until their full
producer chains are checked and assembled.
