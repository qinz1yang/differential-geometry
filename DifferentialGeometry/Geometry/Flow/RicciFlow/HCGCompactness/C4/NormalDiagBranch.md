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

## 2026-07-16 same-source branch coherence

`IsNormalDiag.eqOnSource` proves that two fenced quantitative normal-diagonal
branches with the same center and source radius agree as partial
homeomorphisms.  The proof compares their intrinsic `normalPair` readouts and
uses injectivity of `normalPairHome`; it adds no radius assumption and makes no
claim about equality of unrelated totalized functions.

This is the canonical coherence lemma consumed by
`HasDiagPairConv.congr_stage` to move convergence onto the branch selected by
the minimizing readout.  Focused verification and the targeted module refresh
passed.  `StepB1RawInput` and textbook B1 remain theorem-level **0%**;
dedicated Step-B/B1 machinery is about **95%**, Chapter 4 about **87%**, and
whole-HCG compactness machinery about **57%**.

## 2026-07-18 framed branch migration

The selected branch now consistently uses the orthonormally framed fixed-center
coordinates.  `chart_mem_norm_le` returns `framedChartAt` source membership and
uses `normalFrame_sqrt` with the Gauss radial-length identity, so the obsolete
raw-coordinate coercivity calculation at the origin is gone.  The branch
origin, target recovery, closed-ball fences, controlled pair decoding, and the
common-domain radius chain now use `framedExpDiffeo`, `framedChartAt`, and
`expRadiusGp`.

The raw exponential was not replaced at a moving base point; this file's
changes are confined to coordinates based at the fixed center `x`.  Focused
verification and the targeted module refresh passed, with no local warnings.
This closes a framed consumer seam but does not prove `NormalRadiusProfile`:
that theorem remains 0%, while its dedicated Rm04 machinery remains about 80%.
