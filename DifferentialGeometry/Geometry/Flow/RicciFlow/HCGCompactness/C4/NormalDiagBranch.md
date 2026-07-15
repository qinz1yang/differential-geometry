# NormalDiagBranch

## Role

This module transports the quantitative model normal-phase branch through the
normal tangent and pair coordinates, producing the explicit intrinsic
`DiagInvBranch` used by the HCG lane.

## Current state

- `IsNormalDiag.toBranch` constructs the selected intrinsic branch and carries
  inverse `C^infinity` regularity on the whole transported target.
- `IsNormalDiag.toBranch_hom` exposes the transported partial homeomorphism,
  and `IsNormalDiag.full_transport` proves the exact source-image equality,
  target-image equality, and inverse formula on every point of the full model
  target.  These are proved from `NormalDiagFence`, not left as choice data.
- `IsNormalDiag.pair_mem_of_closed` sends a controlled model closed ball into
  that branch's intrinsic domain.
- `IsNormalDiag.symm_fst_eq` proves that the selected model inverse preserves
  the source normal coordinate on its whole target.  The proof uses the
  compatibility square, `NormalDiagFence`, and injectivity of `normalExpPD`;
  it adds no radius assumption.
- `IsNormalDiag.target_of_pair_mem` recovers model-target membership from
  membership of the realized normal pair in the transported intrinsic domain.
  It is a direct projection from the existing composed partial
  homeomorphism, so it needs neither a new field nor a compatibility wrapper.
- `NormalCoordMetricBoundInput.chart_mem_norm_le` converts the fixed
  Riemannian-distance control into normal-chart membership and an explicit
  coordinate norm bound using the uniform metric-equivalence constant.
- `HasNormalBranchDom`, `exists_pair_branch`, and `exists_common_dom` package
  one common branch for a family of controlled point pairs.
- `HasNormalBranchDom.exists_pair_readout` upgrades the same controlled family
  to `B.readDom` using the canonical exponential target-in-chart property.
- Focused verification passed for both target-recovery helpers; the targeted
  module refresh also passed.  No executable
  `sorry` or `admit` occurs in this module.

## Frontier and accounting

The transported branch, its full-domain equations, inverse formula, and
quantitative `B.readDom` containment are complete.  The next obstruction is not
branch-domain membership: identifying
the selected intrinsic inverse with `normalChartAt` still uses the named
`expDiffeoRadius`, whose intrinsic/realized-exp agreement component is only
pointwise qualitative and has no `NormalRadiusProfile` lower bound.

This is checked infrastructure, not completion of `StepB1RawInput` or the
textbook B1 theorem; both remain 0%.  The explicit selected-branch architecture
acceptance is 100%.  These helpers close a local transport seam but do not
change endpoint accounting; dedicated Step-B/B1 machinery remains about 77%.
