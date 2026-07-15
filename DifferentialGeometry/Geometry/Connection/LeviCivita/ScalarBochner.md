# ScalarBochner.lean

## 2026-06-13

Removed caller-facing `ContMDiffCovariantDerivativeLocally` parameters from
the Levi-Civita scalar Bochner wrappers.  The remaining local smoothness needed
by curvature/commutator inputs is now discharged by the metric producer through
the Levi-Civita curvature wrappers.

Verification: focused check passed.  No new `sorry` or `admit`.
