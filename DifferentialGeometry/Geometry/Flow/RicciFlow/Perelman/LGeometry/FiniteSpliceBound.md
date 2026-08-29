# Uniform finite-chart splice bound

`FiniteSpliceBound.lean` assembles the finite constants needed between the
local chart splice and the late-time reduced-volume floor.

## Result

`redLen_cover_bound` first applies `finite_chart_balls` at a fixed early
forward time.  It takes finite suprema of the chartwise Gram constants, scalar
constants, and coordinate radii returned by `redLen_ball_bound`.  Consequently
one concrete minimizing regularized L-ray produces a measurable target set
whose volume has the fixed positive finite-cover floor and whose reduced length
has one chart-independent explicit upper bound.

The theorem consumes the concrete ray and its reduced-length estimate.  It
does not assume that such a ray exists and does not state a reduced-volume
floor.

## Verification

Focused verification passed without warnings, and the named module artifact
was refreshed successfully.  The source contains no `sorry`, `admit`, or added
axiom.

## Remaining late-time inputs

The next consumer still needs the genuine low-reduced-length ray producer,
the square-root specialization for the two fixed forward slices, and uniform
half-open-terminal-time control of the displayed expression.  After those are
available, `redVolume_set_low` converts this set estimate into the desired
reduced-volume lower bound.

`redVolume_late_low` remains 0%.  The dedicated late-time-floor machinery is
roughly 40--45% complete after this verified producer; generic reused
infrastructure is tracked separately.
