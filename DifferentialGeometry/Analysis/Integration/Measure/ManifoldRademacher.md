# ManifoldRademacher

## Purpose

This module combines Mathlib's finite-dimensional Rademacher theorem with the
generic chart-null transfer. It stays independent of Perelman L-geometry and
does not assert that any particular geometric cost function is Lipschitz.

## Results

`local_diff_ae` is the model-space locality theorem. A map that is locally
Lipschitz on an arbitrary subset of a finite-dimensional real normed space is
differentiable within that subset almost everywhere for the canonical model
Haar measure. Its proof uses local nullity and second countability, so no
single Lipschitz constant on the whole subset is needed.

`chart_nondiff_null` is the fixed-chart layer. If the real-valued function
written in one extended chart is Lipschitz on that chart's target, then the
manifold nondifferentiability set inside the chart source has zero Riemannian
volume.

`chart_local_null` weakens this to local Lipschitz regularity on one chart
target. `nondiff_null` is the compact finite-chart layer: if the function is
locally Lipschitz in every canonical chart, its global manifold
nondifferentiability set has zero Riemannian volume.

The proof uses differentiability relative to the model range, so it does not
add a boundaryless-model assumption. It introduces no new Lipschitz class or
foundational manifold structure.

## Verification

Focused verification passed without warnings or placeholders.

## Project status

The generic manifold Rademacher/null-transfer bridge is complete. The
L-specific local Lipschitz theorem for `lCost`, the two-minimizer implication,
`lCutMulti_null`, and `redVolume_anti` remain separate and are still 0% as
theorem endpoints.
