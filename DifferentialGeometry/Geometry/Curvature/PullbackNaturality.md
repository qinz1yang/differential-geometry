# PullbackNaturality

2026-06-17 HCG/P4 bridge note: exposed the existing cross-domain
pullback naturality proofs as public theorems: `directionalDeriv_pullback` for
scalar metric-component directional derivatives, and `metricCov_pullback` for
the Levi-Civita connection.  These are the scalar-derivative and connection
producers needed before a source-domain pullback comparison for
`metricCovDeriv` towers can be stated honestly.  The existing
`metricRm04Std_pullback` proof now reuses the public connection name instead
of a private helper.

Verification passed for this file; the new public theorem is axiom-clean under
the standard project axioms.
