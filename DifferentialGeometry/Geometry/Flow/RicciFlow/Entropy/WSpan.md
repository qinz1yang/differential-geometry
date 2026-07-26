# Uniform W lower bound on a positive slab

## 2026-07-19 source assembly

`flowW` is the direct time-slice density normal form of Perelman's W
functional.  `w_span_uniform` selects its lower constant from the fixed base
metric `g(a)` before quantifying over the finite upper endpoint; `w_span`
preserves the original one-slab interface as its corollary.  Each slab may use
its own Galerkin radius and finite grid, but neither enters the lower constant.
The scale invariant is `theta + (t - a) < tauMax`.

At each induction step a heat potential is constructed for the fixed horizon
`r`, while W is evaluated after a step of at most `r / 2`.  Consequently the
strict endpoint of `gallim_w_lt` is sufficient, the reflected interval retains
the regular-time buffer `a - a₀`, and no existential lifespan is iterated.
Intermediate slices are passed back to the induction as scalar functions using
`IsHeatPotOn.sliceSmooth`, exact positivity, and exact mass conservation.

The source contains no local `sorry`.  Focused verification is pending the
active upstream spectral export refresh, so `w_span_uniform` and `w_span`
remain theorem-level **0%** with approximately **85%** dedicated source until
checked.  They close the positive-time W lower route once verified.  A uniform
early-time geometric noncollapse producer is still required before the
all-carrier `NoLocalCollapsing` endpoint can be proved.

## 2026-07-23 post-merge check

The finite Good predicate now uses explicit `theta` and `v` binders at the call
sites, and the file opens the L2 namespace needed by the imported W machinery.
Focused verification and the module artifact refresh both passed.
