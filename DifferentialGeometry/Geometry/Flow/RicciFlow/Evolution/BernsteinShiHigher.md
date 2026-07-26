# BernsteinShiHigher

## 2026-07-18 noncompact boundary repair

`BernsteinTower` no longer carries `[CompactSpace M]`.  None of its stored
fields or algebraic/telescoping lemmas uses compactness; only the old global
maximum-principle consumers do.  `[CompactSpace M]` now appears directly on
`BernsteinTower.estimate` and `estimate_div`, preserving their closed-manifold
statements and existing callers.

The edited file passes its focused check, and its module was refreshed for the
new `BernsteinComplete` consumer.  This is an API-boundary repair only; it does
not prove the complete-noncompact maximum principle.

Honest accounting: the structural repair is 100%.  The closed estimate remains
100%.  The separate complete-noncompact estimate is theorem-level 0% until its
cutoff/exhaustion maximum principle is proved.  Unconditional
`compactnessSol` remains theorem-level 0%; whole-HCG support machinery remains
about 60%.

## 2026-07-22 reaction-cost monotonicity

`towerReactionSum_mono` and `TowerHeatBoundOn.mono_cost` now expose the
coefficient monotonicity needed by the corrected arbitrary-dimensional P4
producer.  The proof uses only nonnegativity of the three square-root factors;
it does not assume nonnegativity of the tower fields or hide a cost-domination
claim.  Focused verification passed.

This API brick is complete, but it is only routine infrastructure.  The direct
arbitrary-dimensional `towerHeatSol` theorem remains 0%; its dedicated
machinery is about 60-65%, with the level-zero rough-Laplacian/costed-residual
identity as the first genuine proof frontier.  Complete-noncompact Bernstein
also remains theorem-level 0% pending explicit cutoff/Kato localization.

## 2026-07-22 retained top dissipation

`BernsteinTower.Gfun_dissipative` now factors the pointwise differential
inequality out of the closed maximum-principle proof.  Its conclusion keeps

`2 * t^m * w_(m+1)`

on the left-hand side.  The lower negative tower terms still telescope through
`Wterms_nonpos`; only the top term remains, exactly where a localized proof can
use it to absorb the cutoff-gradient contribution involving `∇w_m`.

The closed `BernsteinTower.estimate` now calls this theorem and discards the
retained term using nonnegativity.  The former duplicated internal reaction and
telescoping proof was removed.  Focused verification passed without local
warnings.

This closes the unlocalized dissipative-algebra brick.  It does not prove the
complete-noncompact estimate: that theorem remains 0%, and its next substantive
frontier is the quantitative parabolic-cutoff producer plus the localized
maximum-principle argument.  The current finite truncation also still needs a
separate prefix-aware repair so that the genuine `w_(m+1)` and only the Kato
levels through `m` are retained.

## 2026-07-22 finite-sum gradient readout

Added `gradientFun_sum`, the reusable identity that the gradient of a finite
scalar linear combination is the corresponding finite linear combination of
the gradients.  The existing gradient-section differentiability theorem now
uses this canonical readout instead of maintaining a second copy of the
inductive identity proof.  Focused verification passed.

This is a routine localization API brick (100%), not a complete-Bernstein
estimate.  It lets `ShiCutoffData.Gfun_cross_le` expand the cutoff-gradient
term of the actual Bernstein polynomial without introducing a supplied
whole-sum estimate.  The corrected complete-noncompact estimate itself remains
theorem-level 0%.

## 2026-07-22 graded coefficient repair

The canonical `towerBeta` coefficient is now `barTop * alpha + m`, rather than
half that value.  No parallel coefficient API was introduced.  The larger
coefficient is what the graded-cutoff recurrence needs to pay both the
time-weight derivative and the top reaction term after part of the tower
dissipation is spent on cutoff gradients.  Existing symbolic consumers retain
their theorem shapes, and the closed Bernstein estimate remains checked.

Added `BernsteinTower.Gcoef_nonneg` as the canonical sign lemma for every
coefficient in `Gfun`.  The source file passes its focused check.  These are
coefficient and algebra infrastructure only: the complete-noncompact estimate
is still theorem-level 0%, while its dedicated localization machinery is about
45--50%.
