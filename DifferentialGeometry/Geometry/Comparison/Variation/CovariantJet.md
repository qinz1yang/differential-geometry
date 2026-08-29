# `CovariantJet.lean`

## Curvature-commutation compatibility name

The global `C∞` convenience theorem is now named `cov_commute_global` and is
verified without warnings.  The canonical name `cov_commute_at` belongs to the
weaker pointwise `C²` producer in `GeneralCurvatureCommutation.lean`.

This is a name-only migration: the global theorem's assumptions, conclusion,
and proof are unchanged.  No compatibility wrapper or additional regularity
assumption was introduced.
