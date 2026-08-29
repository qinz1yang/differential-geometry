# `HigherCurvatureJet.lean`

## Curvature-commutation API migration

The two higher-curvature jet consumers now call `cov_commute_global`, the
global `C∞` convenience theorem from `CovariantJet.lean`.  Both call sites are
verified without warnings and retain their existing hypotheses and proof
shape.

The weaker pointwise theorem keeps the canonical name `cov_commute_at`; this
consumer continues to use the global form because it already has the required
global smoothness data.
