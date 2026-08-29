# Moving-metric time-slab bounds

## Implemented surface

`metric_lower_icc` proves that a jointly continuous family of Riemannian
quadratic forms on a compact time interval and compact manifold has one
positive coercivity constant relative to any fixed smooth reference metric.
The theorem only assumes continuity of `metricTimeBundleQuad`; a smooth metric
family supplies that hypothesis through the existing metric-family API.

The proof reuses the compact moving unit-time slab and
`compactUnitTimeSlab_absBound`.  Applying the latter to the reference metric
gives `gRef(v,v) <= C G(t)(v,v)` with `C >= 0`; the strictly positive choice
`c = (C + 1)⁻¹` also handles empty slabs without a nonemptiness assumption.
Only fully evaluated scalar quadratic forms are compared.

## Verification and next use

Focused verification and the targeted module export pass without warnings.
No new foundational class, bundle representation lemma, or family-smoothness
assumption was introduced.  The immediate consumer is regularized Perelman
L-action coercivity on a compact backward-time slab.
