# Finite coordinate-ball cover

`ChartBallCover.lean` supplies the compact finite-chart step needed after
`redLen_ball_bound`.

## Result

`finite_chart_balls` chooses finitely many coordinate balls covering the
compact manifold.  Each closed coordinate ball stays inside the corresponding
chart target interior, and the inverse-chart open balls share one strictly
positive lower bound for a fixed Riemannian volume measure.  Coverage records
the chart-source and coordinate-ball facts needed by the splice theorem.

## Verification

Focused verification passed without warnings, and the named module artifact was
refreshed successfully.  The source contains no `sorry`, `admit`, or added
axiom.

## Role and progress

This is the finite compact-chart and uniform-volume producer only.  It neither
assumes nor proves the missing reduced-length witness.  The later uniform
reduced-volume floor still has to take finite maxima of the chartwise action
constants, specialize the backward-time arithmetic, and apply
`redVolume_set_low`.

The target theorem `redVolume_late_low` remains 0%.  Its dedicated late-time
floor machinery is roughly 30--35% complete after this verified producer.
