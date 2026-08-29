# MetricFamilyGram

## Role

This module is the fixed-chart geometric producer that turns a smooth metric
family into bounded operator coefficients on the chart model Hilbert space. It
belongs beside `MetricFamilyRegularity`: it does not depend on time-Sobolev
objects, assume an L-geometry curve, or introduce a minimizer-facing wrapper.

## Native route

- `MetricFamilySmoothOn.chartGramOnE_contDiffOn` supplies joint continuity of
  every fixed-chart Gram entry in time and chart position.
- The existing `chartGramBilin` finite expansion packages those entries as a
  continuous bilinear form.
- The existing linear map `IsCoercive.gramCLM` turns the bilinear form into its
  Hilbert-space operator.
- Heine--Cantor on a compact time-coordinate product and Mathlib's uniform
  composition theorem transfer uniform convergence of coordinate curves to
  uniform convergence of the operator coefficients.

## Public API

- `chartGramOp`: fixed-chart metric operator.
- `chartGramOp_inner`: realization of its Hilbert inner product as the metric
  inner product of the inverse chart-trivialized vectors.
- `chartGramOp_change`: invariance of the scalar Gram form under tangent
  coordinate change between two charts containing the same manifold point.
- `chartGramOp_self`: self-adjointness of every fixed-chart Gram operator.
- `chartGramOp_nonneg`: nonnegativity of its quadratic form.
- `chartGramOp_cont`: joint continuity on any time-coordinate subset of the
  regular chart domain.
- `chartGramOp_unif`: uniform coefficient convergence along uniformly
  convergent coordinate curves with eventual compact range control.
- `chartGramOp_bound`: an `NNReal` operator-norm bound on compact products.
- `chartGramOp_lower`: a strictly positive uniform quadratic lower bound on
  compact time-coordinate products contained in the fixed chart target.

## Verification

Focused verification passed without warnings or placeholders, including the
cross-chart Gram invariance theorem.

The lower bound is an internal producer, not a consumer wrapper: it minimizes
the continuous quadratic form on the compact product of the time-coordinate
set with the model-space unit sphere. Membership in the interior chart target
ensures that inverse chart trivialization is injective there, so the minimum is
strictly positive. Empty parameter products and the subsingleton model-space
case are handled separately and require no extra nonemptiness hypotheses.

The canonical-home audit found no import cycle: the historical
`chartGramBilin` module does not import this metric-family operator module, so
the producer can live in `Geometry/Operator` without duplicating the existing
Gram bilinear API.

The realization, self-adjointness, and semidefinite nonnegativity statements
need no chart-target membership hypothesis: the extended chart inverse and its
trivialization map are total, metric symmetry holds pointwise, and positive
definiteness gives nonnegativity after separating the zero vector. Strict
positivity is intentionally not claimed; identifying a nonzero model vector
after inverse trivialization requires the appropriate chart-domain hypothesis.

## Project position

This producer is complete for fixed-chart estimates and pointwise cross-chart
Gram transport (100%). It supplies a reusable
geometric input to the already checked varying-operator weak convergence and
quadratic lower-semicontinuity machinery. The global minimizer theorem and
`redVolume_anti` remain separate, unstated/unproved endpoints (0% each).
