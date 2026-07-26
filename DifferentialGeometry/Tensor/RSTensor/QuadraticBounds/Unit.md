# Unit

## Compact-base metric unit bundle

`metricUnitOn_compact` proves compactness of the metric-unit tangent vectors
whose base lies in an arbitrary compact set.  The proof reuses the existing
finite trivialization cover and local compactness argument; no new topology or
bundle assumption was added.  The former whole-manifold theorem
`metricUnit_compact` is preserved as the `K = Set.univ` corollary.

Focused verification and the exact module refresh pass.  This is reusable
tensor/bundle infrastructure for finite-head compactness estimates, not an HCG
endpoint theorem.
