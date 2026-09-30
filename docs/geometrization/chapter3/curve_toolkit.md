# Metric curve lengths, compactness, and midpoint production

The implementation uses Mathlib's `eVariationOn`, the supremum of sums of
extended distances over finite increasing parameter lists. On a continuous
curve over the unit interval this is its metric length, with infinity allowed.
It is not the Riemannian integral of a speed and makes no differentiability
assumption. Mathlib's definition explicitly supplies the partition convention.
No second curve-length definition or competing Riemannian API is introduced.

`Metric.eVariationOn_le_liminf_of_pointwise` gives lower semicontinuity under
pointwise convergence on the specified ordered parameter set. It allows
infinite limit length, a nontrivial arbitrary index filter, and pseudoemetric
targets. The proof applies the library's fixed-finite-partition semicontinuity
lemma and the exact order-theoretic liminf criterion.

`Metric.eVariationOn_Icc_le_of_lipschitzOnWith` bounds the length of a
C-Lipschitz function on [a,b] by C times max(b−a,0), expressed in extended
nonnegative reals. C=0 and an empty interval are covered. It uses Mathlib's
composition inequality and the computed variation of the identity.

`Metric.exists_subsequence_tendstoUniformly_of_lipschitz` gives a strictly
increasing subsequence with a uniform limit, retaining the common Lipschitz
constant and membership in a fixed compact target set. The parameter space
can be any compact metric space, not only [0,1]. No target completeness or
continuity hypothesis beyond that already implied by Lipschitz is added.
The proof applies Mathlib's Arzela–Ascoli theorem to bounded continuous maps.

`Metric.exists_approximate_midpoint_of_curve` turns a continuous unit-interval
curve of length <d(a,b)+2h, h>0, into a point at distance <d(a,b)/2+h from
each endpoint. The intermediate value theorem gives equal endpoint distances;
the sum of the two distances is bounded by variation using interval additivity.
`Metric.approximate_midpoints_of_arbitrarily_short_curves` applies this to
exactly the near-short-curve characterization of a length metric.

The actual consumer is
`PointedGHConverges.exists_metric_segment_of_source_curves`: every proper
pointed limit of metric spaces admitting arbitrarily short curves has a
continuous, distance-realizing segment between every pair. The curve inputs
use actual supplied source distances. Source properness is not assumed.

Sources: blueprint207A MC01, MC21 and MC23; unchanged source/errata records
reference_checks_revision58.md, reference_checks_revision59.md and
metric_geometry_contracts.csv. BBI Proposition2.3.4(iv), printed35/PDF50
(with errata2), and Theorem2.5.14, printed47–48/PDF62–63 (with errata3).
The blueprint's displayed midpoint argument was read. Target Mathlib's
BoundedVariation, IntermediateValue and ArzelaAscoli theorem bodies/signatures
were inspected. No fresh full-book or Riemannian arclength audit is claimed.

The scoped build and axiom gate verify these leaves and their consumers.
