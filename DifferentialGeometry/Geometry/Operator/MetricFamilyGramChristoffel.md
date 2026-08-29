# MetricFamilyGramChristoffel

## Status

`chartGram_spatial` is complete and focused verification passes without warnings.
It is a reusable scalar producer for the fixed-chart spatial derivative of a
smooth metric-family Gram operator.

The eventual consumer `lChartEuler_iff` is still not proved by this file (0%).
This lower-layer producer itself is complete (100%). It closes the previously
missing spatial-Gram/Christoffel bridge in the dedicated chart-Euler machinery;
the remaining chart-Euler assembly still needs the time derivative, scalar
gradient, and phase-field/covariant-acceleration identities.

## Native route

The proof remains fully scalar after applying the Gram operator to fixed vectors.
It reuses:

- `chartGramOp_smooth` for differentiability of the operator family;
- `chartGramAlongCurve_hasDerivAt_covariant`, whose checked proof is built from
  the native `chartGramOnE` partial-derivative and Christoffel component APIs;
- `chartGramBilin_apply` only to identify the two scalar Gram sums;
- `chartGramOp_self` for the final symmetry of the two metric pairings.

The auxiliary manifold curve is the inverse-chart image of the affine model-space
line `y + s • w`. On the interior chart target, the chart right inverse makes its
chart curve eventually equal to that line. Derivative uniqueness then identifies
the Frechet spatial derivative pairing with the two covariant Gram pairings.

No mixed-tensor/Hom representation is unfolded, and no reference-tree module is
imported.

## Iteration notes

The direct four-index finite-sum expansion was not needed. The only failed proof
iterations were local elaboration issues: the Gram scalar rewrite needed an
explicit `chartGramBilin_apply` specialization, the one-dimensional chain rule
needed `comp_hasDerivAt_of_eq`, and the self-adjoint identity needed a final real
inner-product symmetry. None exposed a missing API.
