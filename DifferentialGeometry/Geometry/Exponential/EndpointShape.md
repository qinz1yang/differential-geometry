# EndpointShape

## 2026-07-23 fixed-first endpoint shape

This file is the branch-selected, second-order endpoint layer for the canonical
intrinsic exponential.  The source now contains:

- `intrinsicJacobi`, the affine initial-velocity variation field;
- `intrinsicJacobi_perp`, the endpoint Gauss identity
  `g(γ'(1),J_w(1)) = g_p(u,w)`;
- `endpointJacobi_eq`, the branch-free derivative formula for the normalized
  terminal radial velocity;
- `branchHess_jacobi`, the selected-branch Hessian formula including its
  rank-one normalization correction;
- `branchHess_shape`, the perpendicular shape-operator specialization;
- `intrinsicJacobi_li`, injectivity of the endpoint Jacobi family on a selected
  fixed-first inverse branch.

The Hessian proof uses the canonical `BranchRadius.branchRadius_open` producer,
the local chart-Hessian/covariant-gradient bridge, mixed variation
commutation, and `IntrinsicGauss.intrinsic_gauss`.  It does not use a raw
exponential radius, global minimality, or a `ConnectedSpace` hypothesis.

Focused verification is green with no diagnostics.  The formerly fragile
dependent rewrite in `branchHess_jacobi` is now factored through one
tangent-vector identity and then paired with the endpoint Jacobi vector; the
remaining normalization is ordinary real-field algebra.  The private launch
derivative also carries only the section assumptions it uses.

The Layer-B endpoint theorem and its dedicated machinery are therefore 100%:
focused verification and the exact module refresh are both green.  The
comparison-facing `radialLap_eq_mean` theorem remains 0% until the downstream
radial module is checked; whole HCG supporting machinery remains roughly 60%,
and unconditional `compactnessSol` remains 0%.

## 2026-07-24 canonical fixed-first branch

`branchHess_jacobi`, `branchHess_shape`, and `intrinsicJacobi_li` now consume
`ExpInvBranch` directly. Their source neighborhoods live in the fixed model
tangent space, and the inverse readout is `B.inv`; the old tangent-bundle
pair packaging was inherited from `DiagInvBranch` and is no longer part of
the proof-owning API.

The migration is focused green and placeholder-free. The underlying endpoint
Hessian theorem and its dedicated machinery remain 100%; the later
`calabiDist_support` theorem is still unstated (0%). Route B-prime remains
about 45%, whole HCG supporting machinery about 60%, and unconditional
`compactnessSol` theorem-level 0%.
