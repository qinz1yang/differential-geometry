# ChartNull

## Purpose

This module places the one-chart null-set transfer at the generic measure
layer.  It is independent of the elliptic Hessian consumer and of Perelman
L-geometry.

## Result

`chart_preimage_null` says that a Euclidean set whose intersection with the
Euclidean chart target has zero Lebesgue measure pulls back, on the chart
source, to a set of zero Riemannian volume.  The set itself need not be known
measurable: the proof passes to a measurable null superset.

`chart_model_null` gives the directly compatible version for a set in the
manifold model space measured by `modelHaar`.  It transports the null set by
the canonical `toEuclidean` measurable embedding and then applies the
Euclidean theorem.

`finite_chart_cover` extracts a finite cover by canonical chart sources on a
compact charted space.  `null_of_chart_cover` combines nullity of the finitely
many chart pieces into global nullity for an arbitrary measure.

The proof reuses the existing chart-local integration bridge and the equality
between the global Riemannian volume restricted to a chart source and the
chart-local measure.  No new measure-space instances or analytic hypotheses
are exposed globally.

## Verification

Focused verification passed without warnings or placeholders.

## Project status

This closes the single-chart null transfer and compact finite-chart
localization infrastructure needed by the conjugate cut-image route.  The
L-specific Sard producer and its final finite-cover assembly remain separate
consumer work.  The cut-image null theorem and `redVolume_anti` remain at 0%
until their Lean declarations are proved.
