# Ricci drift

## 2026-07-16 weighted divergence producer

This module defines the canonical Ricci-gradient one-form/vector and proves the
two scalar identities consumed by the weighted Hessian calculation:
`ricDriftDiv` for its divergence and `ricDriftAct` for its action on the
potential.  The proofs use `metricNablaSymm` and fully evaluated scalar
contractions; no dependent whole-tensor equality or new consumer assumption is
introduced.

Focused verification passed without a local `sorry`.  These producers and
their dedicated machinery are 100%; Perelman no-local-collapsing remains a
separate theorem-level 0% frontier.
