# SmoothNLC

## Role

This module begins the ordinary smooth-flow no-local-collapsing argument.  Its
first producer is the set-level reduced-volume lower bound used in the opening
step of Morgan--Tian `noncoll.tex`: an upper bound for reduced length on a
measurable slice set turns into a lower bound for reduced volume by the exact
standard normalized reduced density.

## Implementation

`redVolume_set_low` stays at the consumer-facing `SmoothNLC` layer rather than
changing the settled `ReducedVolume` module.  It uses the current definition of
`redDensity` directly, restricts the reduced-volume integral to the measurable
set, and compares there with the constant obtained by replacing reduced length
by its supplied upper bound.  It does not assume Ricci-flow regularity, positive
backward time, connectedness, or any curvature hypothesis because none is
needed for this measure-theoretic implication.

## Status

Focused verification is warning-free green.  The theorem `smooth_nlc` remains
unstated and unproved (0%).  The first reduced-volume producer
`redVolume_set_low` is **100%** for its stated interface.  The upstream
`redVolume_anti` and `redVolume_zero_lim` capstones are each **100%** and
focused-check green.  Dedicated L8--L9 smooth-noncollapsing machinery is about
76--78%;
the already checked L-geometry and generic integration machinery it consumes
are separate and are not counted as completion of `smooth_nlc`.

Both fixed-time producer branches are now complete. `redVolume_late_low`
provides the positive floor uniformly on the half-open late-time interval, and
`redVolume_ball_eta` supplies an arbitrary positive Gaussian-tail error at one
terminal time. The remaining gap is that the short-scale threshold in the
ball estimate is still chosen after fixing the terminal time.

The late floor removes the former varying-parameter compactness branch.  The
remaining chain is now

```text
shiRm1_ball -> lGrad_ball -> lRegSpeed_unif
  -> lMetric_ball + lRegRange_unif -> lExp_ball_unif
  -> redVolume_ball_unif + redVolume_late_low
  -> IsKappaNoncollapsed -> smooth_nlc.
```

Direct `smooth_nlc` assembly therefore meets a narrower honest missing-API
stop rather than a Lean elaboration blocker.  The lowest missing analytic
producer is `shiRm1_ball`: from an Rm bound on a parabolic ball it must bound
the first covariant derivative of Rm by `C / r^3` on a strictly smaller
cylinder.  The downstream adapter `lGrad_ball` must give the corresponding
scalar-gradient pairing bound on the later half-time interval and half-radius
ball, with `C` chosen before terminal time, center, and radius.  These interior
losses are essential; a bound up to the boundary of the same cylinder would be
false as a local Shi statement.

The existing `movingShiBoundN`, `movingShiBoundSol`, `movingShi_of_bound`,
`movingShi_complete`, and `movingShi_open` were checked and all assume
curvature control at every spatial point before concluding on `Set.univ`.
Restriction and pullback only transport an already supplied Shi bound, while
the available Shi cutoff is likewise built from a global curvature bound.
Thus none produces `shiRm1_ball` from `FlowMetricBall.IsRmControlled`.
A finite cover also cannot replace it because `[a, omega)` is not compact and
the fixed-slab thresholds have no positive uniform lower bound as their right
endpoints approach `omega`.

This is a substantial spatial-cutoff/local-maximum-principle API frontier, not
a routine adapter or coercion issue.  Once `shiRm1_ball` exists, `lGrad_ball`
can reuse the checked Ricci trace, contracted Bianchi, scalar-gradient, and
tensor-norm APIs; `lMetric_ball` uses existing Ricci quadratic and moving-metric
comparison machinery and is not a second analytic frontier.  The final
`poincare_of_inputs` theorem remains 0%; full-program infrastructure is
estimated at 15--25% under the P0--P9 workload denominator.
