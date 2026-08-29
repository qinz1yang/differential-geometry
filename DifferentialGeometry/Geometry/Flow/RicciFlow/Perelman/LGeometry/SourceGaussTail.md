# SourceGaussTail

## Role

`lSrcGauss_tail` is the quantitative source-tail producer for the good/bad
L-exponential-source split.  It says that the `modelHaar` integral of the exact
normalized `lSrcGauss` density outside terminal-metric balls tends to zero as
the radius tends to infinity.

## Route

The proof packages the source Gaussian as the `withDensity` measure over the
canonical `modelHaar`.  Its total mass is exactly one by `lSrcGauss_mass`.
Terminal-metric radius sublevel sets are measurable because the pointwise
metric is a continuous bilinear form, and they exhaust the source tangent
space.  Continuity from above for the resulting finite measure then gives the
vanishing complement mass.  No tail estimate, alternate Haar normalization,
or additional geometric hypothesis is assumed.

## Status

Focused verification and the targeted module refresh previously passed without
warnings or proof placeholders for `lSrcGauss_tail`, which remains **100%** for
its stated interface.

The new `lSrcGauss_unif` source adapts the exact generic SPD change of variables
to `modelHaar`.  It selects one nonnegative terminal-source radius for any
positive tail threshold, uniformly in the solution data, terminal time, and
basepoint.  Its focused verification passes without warnings or placeholders,
and the named module artifact has been refreshed.  The declaration is **100%**
for its stated interface.  The refresh replayed only pre-existing linter
warnings in unrelated upstream modules.

The target theorem `redVolume_ball_le` is still unstated and unproved (**0%**),
and its dedicated good/bad-split machinery is about **15--20%** once the
already verified pointwise tail comparison is counted separately.  The capstone
`smooth_nlc` remains unstated and unproved (**0%**); this producer is dedicated
machinery for that route and does not count as completion of the capstone.

After verification, the scale-uniform endpoint theorem can choose its small
backward-time parameter from this common source radius, and the bad-source term
can be bounded by the selected threshold rather than only by a pointwise
`Tendsto` statement.
