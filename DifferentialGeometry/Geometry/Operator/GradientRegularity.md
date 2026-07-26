# GradientRegularity.lean - realized-gradient regularity

## 2026-07-24

The existing global producer `gradientFun_smooth` was not directly usable for
a scalar known to be smooth only on an open inverse-branch target.  The private
coordinate proof already depended only on a germ at the evaluation point, so
its input was narrowed from global `ContMDiff` to `ContMDiffAt`.

Added `gradientFun_mdiffOn`: if `U` is open and `f` is `ContMDiffOn` of order
infinity on `U`, then the total-space section realizing `gradientFun g f` is
manifold-differentiable at every `x` in `U`.  The global APIs remain unchanged
and now reuse the narrower private producer.

Focused verification passed with no diagnostics.  The new theorem and its
dedicated regularity machinery are complete (100%).  This closes only the local
gradient-regularity input needed by `laplacian_add_const`;
`calabiDist_support` remains separately at theorem level 0%.  No targeted
module refresh was run in this lane.

## 2026-07-24: composition germ

Added `grad_comp_mdiffAt`, which transfers differentiability of the realized
gradient through a smooth scalar outer function using only neighborhood
differentiability of the inner scalar and pointwise regularity of its gradient.
It is the route-neutral chain-rule input used by the barrier cutoff.

Focused and exact verification are current with no diagnostics.  This theorem
and its dedicated regularity machinery are 100%; it does not by itself
complete the geometric cutoff producer.
