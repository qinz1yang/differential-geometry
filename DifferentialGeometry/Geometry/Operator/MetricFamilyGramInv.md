# Metric-family Gram inverses

`MetricFamilyGramInv.lean` proves pointwise invertibility, continuity, and
joint smoothness of the inverse fixed-chart Gram operator.  The proofs obtain
coercivity from the existing compact lower-bound theorem on singleton
time-coordinate sets.  Continuity uses the native normed-ring inverse theorem;
`chartGramInv_smooth` combines `chartGramOp_smooth`, `chartGramOp_unit`, and
Mathlib's smoothness of ring inversion at a unit.

Focused verification and the targeted module refresh for the new smooth
inverse theorem passed without warnings.  `chartGramInv_smooth` and its
dedicated inverse-regularity assembly are complete (100%).
