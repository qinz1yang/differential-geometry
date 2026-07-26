# ConjCriticalSpan

## Goal

Provide the critical finite-core energy inequality on every requested backward
interval below one radius chosen uniformly over a compact regular-time slab.
The theorem must not select a second, smaller lifespan after the caller chooses
the interval length.

## 2026-07-19 compact-span assembly

`scalar_crit_span` combines the prescribed-length `cc_a2_span` producer with
the existing compact-parameter `cc_a1_unif` scalar-potential estimate.  The
terminal metric and spectral space are formed only after the base time is
chosen.  The lower constants may depend on that base time and Sobolev order,
but not on spectral support or Galerkin cutoff.

The proof retains the verified top coefficients `5/3` and `1/4`, hence the
combined coefficient is `23/12 < 2`.  It introduces no consumer assumption,
whole-space comparison between different terminal metrics, or
`HasLocallyConstantChartAt` hypothesis.

Verification is pending the in-progress targeted refresh of the newly public
compact-span Garding producers.  The next consumer, once this file checks, is
a prescribed-length Galerkin existence/energy/subsequence assembly rather
than another existential short-time wrapper.

Honest accounting: `scalar_crit_span` is theorem-level 0% until focused
verification passes; its dedicated source and machinery are approximately
99%.  `gal_span`, `gallim_on`, target-length positivity/mass, the finite Good
induction, `NoLocalCollapsing`, and `ham3_noncollapse` remain theorem-level 0%.
Broader noncollapsing machinery is approximately 97%, and whole HCG machinery
approximately 60%.

## 2026-07-23 post-merge check

The local model typo in the `hζ` differentiability statement was corrected to
`𝓘(Real, Real)`.  Focused verification and the module artifact refresh both
passed.
