# WVariation

## 2026-07-16 raw first variation

`w_rev_hasDerivAt` is checked.  Its inputs are the actual reversed Ricci-flow
metric, the actual `conjCoeff S (T - r)` conjugate-heat coefficient, a positive
`IsHeatPotOn` solution, and only the regular-time conditions needed at the
evaluation time.  The coefficient is reduced internally by `conjCoeff_apply`;
no parallel heat equation or supplied regularity package is exposed to the
consumer.

The proof stays scalar and interval-local.  On the open regular-time patch it
uses `potential_joint`, `revGram_smooth`, `gradSq_joint`, and `scalar_joint` to
feed `first_var_joint`.  The pointwise derivatives are supplied by
`potential_pde`, `revScalar_time`, `revGradSq_time`, and `revTrace_eq`.
`wFunctional_base` performs only the weighted-measure-to-base-measure conversion;
it now lives publicly in `Defs.lean` because later fixed-metric estimates need
the same canonical normal form.
No global frame, whole tensor/Hom equality, `HasLocallyConstantChartAt`, or new
consumer assumption is used.

Focused verification passed without a new `sorry`.  The raw theorem
`w_rev_hasDerivAt` and its dedicated first-variation machinery are 100%.
Weighted Hessian square completion and W monotonicity remain theorem-level 0%;
Perelman no-local-collapsing and `ham3_noncollapse` remain 0%.  Broader
entropy/noncollapse machinery is approximately 67%, while whole HCG machinery
remains approximately 60% with its endpoints at 0%.

The next exact producer is `ricDriftDiv`, followed by
`weighted_hess_split`.  `hessSec_inner_cov` and `ricHess_eq_inner` are checked;
the remaining low-level adapters are the canonical scalar-curvature bridge and
the public orthonormal trace formula needed by the divergence calculation.

## 2026-07-16 square and derivative sign

`w_rev_square` is checked.  It converts the actual raw reverse-flow variation
to the canonical weighted square through a scalar base-measure/
`e^{-f} dmu` bridge and `weighted_w_square`.  `w_rev_deriv_nonpos` then proves
that the actual `deriv`-based first variation is nonpositive at every positive
regular time covered by the hypotheses.  No dimension, chart, supplied
regularity, or other consumer assumption was added.

Focused verification passed without a local `sorry`.  The raw first variation,
weighted square, and local derivative-sign theorems are each 100%, as is their
dedicated machinery.  A separate interval-level `MonotoneOn` wrapper is not yet
stated (0%), and the cutoff contradiction, Perelman no-local-collapsing, and
`ham3_noncollapse` remain theorem-level 0%.  Broader entropy/noncollapse
machinery is approximately 75%; whole HCG machinery remains approximately 60%
with its endpoint theorems at 0%.

## 2026-07-16 interval monotonicity

`w_rev_antitone` is checked.  On every positive closed reverse-time interval
contained in the reverse and original regular-time domains, it combines the
actual square first variation with the derivative mean-value theorem to prove
`AntitoneOn` for the genuine reversed-flow `W` path.  This is the interval
theorem required by the noncollapsing route; no global regularity, chart
selector, dimension, or supplied monotonicity assumption was introduced.

The raw first variation, square identity, derivative sign, and interval
antitonicity theorems are each **100%**, together with their dedicated
machinery.  The fixed-metric W lower bound, cutoff contradiction, Perelman
no-local-collapsing, and `ham3_noncollapse` remain theorem-level **0%**.  The
next honest analytic producer is a uniform closed-manifold Sobolev constant,
then a fixed-metric log-Sobolev/W lower bound.  Broader entropy/noncollapse
machinery is approximately **78%**; whole HCG machinery remains approximately
**60%**, with its endpoint theorems at **0%**.

## 2026-07-17 Galerkin zero-endpoint W continuity

The source proof of `gallim_w_cont` has been assembled. It consumes the verified
closed-interval scalar and gradient-square continuity from
`ConjGalerkinClassical`, shrinks independently into the terminal regular-time
window, rewrites the potential-gradient square with `potential_grad_sq`, and
rewrites `wFunctional` against the ordinary moving Riemannian measure before
calling `integral_family_cont`. The statement adds no regular-window or
endpoint-convergence assumption; positivity and the positive W offset are the
only scalar hypotheses needed for reciprocal and logarithm continuity.

Verification is not yet observed. The first check saw only stale-import errors
because the newly exported Galerkin declarations were absent from the old
upstream object. The explicit upstream refresh is still actively rebuilding its
dependency chain, so the W theorem itself has not yet produced a Lean proof
diagnostic. The next exact step is one focused check after that refresh lands,
then local repairs only.

Honest accounting: `gallim_w_cont` is theorem-level **0%** until checked, with
its source proof assembled; its dedicated endpoint machinery is about **85%**.
The subsequent zero-endpoint antitonicity comparison remains unstated and
theorem-level **0%**. Perelman `NoLocalCollapsing` and `ham3_noncollapse` remain
theorem-level **0%**; broader entropy/noncollapsing machinery is about **97%**,
and whole HCG machinery about **60%**.

## 2026-07-18 verified Galerkin W continuity

`gallim_w_cont` now passes focused verification. The stale Galerkin object was
refreshed, after which the remaining repairs were only namespace qualification,
an explicit denominator-nonzero application before `ContinuousOn.log`, and a
function-level rewrite of the potential gradient square. The theorem statement
and its assumptions were unchanged.

The existing `Entropy/F` layer was also audited. The current W-square route
already reuses its `weightedGreen` and `weighted_grad_zero` results through
`WeightedHessian.lean`; these are canonical supporting APIs rather than a
parallel unused implementation. The Formula-5.10 producer/final chain concerns
the `F` functional and does not replace the Galerkin endpoint continuity or the
finite-horizon W comparison.

Honest accounting: `gallim_w_cont` is theorem-level **100%**, and its dedicated
endpoint-continuity machinery is **100%**. The zero-endpoint antitonicity
comparison remains theorem-level **0%**. Perelman `NoLocalCollapsing` and
`ham3_noncollapse` remain theorem-level **0%**; broader entropy/noncollapsing
machinery remains about **97%**, and whole HCG machinery about **60%**.

## 2026-07-18 zero-endpoint W comparison

`gallim_w_le` now passes focused verification.  It independently shrinks the
Galerkin interval into the terminal regular-time window, shifts the classical
heat-potential solution to a positive original-time interval, applies the
checked positive-time theorem `w_rev_antitone`, and extends the comparison to
reverse time zero through `gallim_w_cont`.  The only new local helper is the
generic real-valued fact that a continuous function on `[0,b]` which is
antitone on `(0,b]` is bounded above by its value at zero.

The proof keeps every shifted-object identification fully scalar and applied;
it does not ask Lean to compare whole dependent tensor or Hom objects.  No
regular-window, convergence, chart-selector, or supplied monotonicity
assumption was added.

Honest accounting: `gallim_w_cont` and `gallim_w_le` are each theorem-level
**100%**, and the local zero-endpoint comparison machinery is **100%**.  The
terminal-uniform Galerkin span `gal_span`, target-length classical existence
`gallim_on`, and finite-horizon comparison `w_span` remain theorem-level
**0%**.  Perelman `NoLocalCollapsing` and `ham3_noncollapse` remain
theorem-level **0%**.  Broader entropy/noncollapsing machinery remains about
**97%**, and whole HCG machinery about **60%**.

The subsequent compact-span audit found that the span should be built only on
a compact interval contained in `D.regular`, starting from a fixed positive
time where `w_fixed_lower` is available.  A version whose final step reaches
the initial carrier endpoint is not justified by the current `C0`-only
endpoint metric regularity.  The remaining missing producer is the compact,
joint varying-background order-one metric modulus recorded precisely in
`Perelman/Noncollapsing.md`; it is not another W-variation lemma.
