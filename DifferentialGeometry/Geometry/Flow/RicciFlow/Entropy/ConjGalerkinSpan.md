# Compact-span scalar Galerkin compactness

## 2026-07-19 source assembly

`gal_span` is the intended terminal-uniform interior producer.  It takes a
compact slab `Icc a b` contained in the regular times and selects one positive
radius before any terminal metric or spectral space is formed.  For every
caller-selected `h` below that radius, it combines `lapA20_span`,
`scalar_crit_span`, and `conjA1_on`, then calls the exact-interval producers
`gal_exists_on`, `gal_bound_on`, and `gal_subseq_on`.

Only the two slab radii are minimized.  After the caller chooses `h`, no proof
step shortens the interval.  The hypothesis `a ≤ T - h` is retained, so this
theorem does not claim first metric-jet control at a nonregular initial
endpoint.  All spectral types are formed after `T` is introduced; no equality
or transport between Sobolev spaces for different terminal metrics occurs.

The source contains no local `sorry` and introduces no consumer assumption,
chart-selector hypothesis, or global heat object.  Focused verification is
pending the active upstream spectral object refresh.  Accordingly `gal_span`
is theorem-level **0%** and its dedicated source machinery is approximately
**98%** until the exact file check passes.

`gallim_span` now combines that terminal-uniform Galerkin producer with the
exact finite-core identity and returns a genuine `IsHeatPotOn` object on every
caller-selected interval.  `gallim_unit_span` chooses the existing smooth
positive unit initial density and adds exact positivity and mass conservation
through the entire interval.  Neither theorem makes a second lifespan choice.

These two declarations also contain no local `sorry`, but remain theorem-level
**0%** pending focused verification; their dedicated source is approximately
**95%**.  The next analytic frontier is exact-interval W comparison, followed
by finite Good-set propagation on the positive compact slab.

## 2026-07-23 post-merge check

The span assembly now opens the measure namespace, splits the current `hgal`
interface into its regularity and subsequence components, and marks the
caller-supplied positive time step binder unused.  Focused verification and the
module artifact refresh both passed.
