# RiemannFromRicci.lean

## 2026-06-13

Removed the local smoothness hypothesis from the dimension-three
Levi-Civita-realized algebraic curvature symmetry wrappers.  They now consume
only the metric and curvature realization data, relying on the lower
Levi-Civita symmetry wrappers to discharge local smoothness.

Verification: focused check passed and the module was rebuilt for downstream
signature refresh.  No new `sorry` or `admit`.
