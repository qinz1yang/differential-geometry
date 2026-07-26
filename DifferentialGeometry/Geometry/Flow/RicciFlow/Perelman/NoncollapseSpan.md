# NoncollapseSpan

## 2026-07-19 positive-slab endpoint

`noncollapse_span` is the honest fixed-positive-slab form of Perelman's
noncollapsing argument.  It combines the compact-slab W lower bound from
`Entropy/WSpan.lean` with the selected curvature-controlled cutoff density from
`FlowBallW.lean`.  The noncollapsing constant is
`exp (L - collapseWConst n - 1)`; the last step first proves the real normalized
volume bound and then maps it into `ENNReal`.

The proof reuses the public explicit-ball positivity theorem
`VolumeComparison.edist_vol_pos`; no positive-volume or finite-volume
assumption is added to the consumer theorem.  The result applies uniformly to
times in `Icc a b` when `a₀ < a`, `Icc a₀ b` is regular, and ball radii are
bounded by `rho`.

Static signature and proof-normal-form review passed.  Focused verification is
pending because the newly exported W-span dependency has not yet been
refreshed; a bounded isolated probe produced no diagnostic before it was
stopped to avoid competing with the active shared build.  This theorem does
not close `NoLocalCollapsing`, whose
all-flow-time statement still requires a uniform entrance estimate as time
approaches the initial boundary.

Honest accounting: `noncollapse_span` is source-complete but remains 0% at the
verified theorem level until its focused check passes.  Its dedicated proof
assembly is about 95%.  `NoLocalCollapsing` and `ham3_noncollapse` remain 0%;
the broader entropy/noncollapse machinery is about 97%, and the whole HCG
compactness project remains about 60%.

## 2026-07-23 post-merge check

`noncollapse_span` now supplies the explicit unit `δ`, rewrites the scalar
curvature trace with `SolutionOn.scalar_eq_metricTrace`, and uses the correct
division-inequality direction in the final denominator move.  Focused
verification and the module artifact refresh both passed.  This closes the
positive regular-slab span theorem, but the global endpoint still needs the
initial-time entrance/noncollapse producer.
