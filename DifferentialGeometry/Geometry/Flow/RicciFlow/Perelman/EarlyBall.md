# EarlyBall

`EarlyBall.lean` supplies the initial-boundary producer for Perelman
noncollapsing on a half-open short-time interval.

`early_vol_low` is now a checked Ricci-flow adapter from the metric-family
producer `VolumeComparison.family_vol_low` to the explicit flow metric family.
`early_ball_low` is a checked adapter from `early_vol_low` to
`FlowMetricBall.IsKappaNoncollapsed`. `no_local_open` assembles the final
all-carrier `NoLocalCollapsing` predicate from `early_ball_low` and the verified
positive-time theorem `noncollapse_after`. Its proof is only the
early/positive-time case split and the minimum of the two kappa constants.

Verification status: the focused check passed without warnings after
`FamilySmallBall` was refreshed. `family_vol_low`, `early_vol_low`,
`early_ball_low`, and `no_local_open` are all source-complete without a local
`sorry`; the original-flow all-carrier `NoLocalCollapsing` theorem and its
dedicated initial/positive-time assembly are therefore 100%.

This is not yet an axiom-clean import closure. The positive-time branch
`noncollapse_after` ultimately consumes the remaining Weyl diagonal-kernel
counting `sorry` in `ShortTime/WeylEigenvalueCountingBound.lean`. That analytic
producer, rather than initial-time geometry, is now the smallest honest
noncollapsing dependency frontier.

Historical route audit: the global Rm04 volume-comparison route was rechecked against
`Comparison/Volume/BallVolume.lean`.  The strongest packaged theorems such as
`exists_vol_globalRm1` and `exists_vol_rm1_ge` still return a normal/radial
radius depending on the centre `p` and require scalar launch/model inputs at
that centre.  They do not by themselves give the all-centre uniform radius
needed by `early_vol_low`. The implemented fixed-parametrization finite-cover
route avoids that detour.

## 2026-07-23 axiom-clean closure

The earlier Weyl caveat is superseded. All nine rank-zero Galerkin tail
consumers now use the proved scalar producer `scalar_eigen_tail`; the deferred
generic tensor local-Weyl theorem is no longer in the Entropy/Perelman source
dependency graph.

The full `EarlyBall` dependency artifact refresh passed, and the axiom audit of
`no_local_open` reports only `propext`, `Classical.choice`, and `Quot.sound`.
Thus `NoLocalCollapsing` on the original half-open flow interval is
theorem-level **100%**, and its dedicated early/positive-time machinery is
**100%**. This does not complete the separate HCG compactness or
limit-classification endpoints.
