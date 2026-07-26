# HeatHessL2

## Proved layer

This file supplies the exact Plancherel anchor for the singular heat-Hessian
arm.  Spacetime is represented by `WithLp 2 (ℝ × V)`, because the ordinary
product type carries the max norm and therefore is not a real Hilbert space.
The imported volume-preserving measurable equivalence identifies this Hilbert
product with the ordinary measurable product when the later convolution
realization is proved.

The checked source proves:

- `heatHessSym`: the scalar complex Fourier symbol of
  `∂_v ∂_w (∂_t - Δ)⁻¹`, with Mathlib's `2π` Fourier normalization;
- `heatHessSym_norm`: the sharp pointwise bound
  `‖m_{v,w}‖ ≤ ‖v‖ ‖w‖`;
- Borel measurability and membership of the symbol in spacetime `L∞`;
- `heatHessFreq_norm`: the induced frequency-side multiplication estimate on
  `L²`;
- `heatHessL2_fourier`: the exact Fourier-side representative of the
  multiplier;
- `heatHessL2_norm`: the Plancherel estimate
  `‖T_{v,w} f‖₂ ≤ ‖v‖ ‖w‖ ‖f‖₂`.

There are no assumptions encoding the desired estimate, and no
`sorry`/`admit`/axiom/opaque declarations.

## Exact remaining realization boundary

This file does **not** yet identify `heatHessL2` almost everywhere with the
causal convolution `heatD2Duh` / the directional evaluation of `heatGrad1` on
a smooth compactly supported source.  The smallest missing theorem is the
Fourier transform identity for that causal convolution, including the
zero-extension in time and the passage through both Bochner integrals.  No
such identity currently exists in the Euclidean heat-kernel API.

Three routes were considered:

1. absolute time integration of the fixed-time `heatD2Lp_norm` bound fails at
   the genuine nonintegrable `(t-s)⁻¹` singularity;
2. a direct spacetime energy proof needs a new weak heat-equation realization
   and integration-by-parts layer;
3. Fourier realization is the faithful shortest route, but still requires the
   Gaussian spatial transform, the causal one-sided time transform, and
   Fubini/density passage for the existing integral definition.

Accordingly, the reusable `L²` multiplier machinery is complete, while the
causal-convolution realization theorem is 0%.  The later fixed-`p`
Calderón--Zygmund extension and the endpoint Ricci-flow theorems remain 0%.

## Verification

Focused Lean check: GREEN, with no local warnings.
