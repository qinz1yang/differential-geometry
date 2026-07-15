# Uniform scalar Galerkin energy bounds

## Role

`ConjGalerkinEnergy.lean` is the finite-dimensional energy producer between
the scalar Galerkin ODE construction and the later Galerkin compactness/limit
argument.  Its target theorem is `scalar_gal_bound`.

The statement uses one interval independent of the smooth scalar initial datum
and of an arbitrary sequence of finite spectral sets.  It returns one
coefficient solution for every truncation, preserves the genuine smooth
initial coefficients, records zero coefficients off each finite set, and gives
an all-order `galerkinEnergy` bound uniform in the truncation index.

## Source route

The source proof combines four existing producers:

- `scalar_gal_exists` supplies each finite coefficient solution on a common
  interval;
- `scalarGalPert_fin` identifies the abstract perturbation coefficients with
  the fully geometric moving-Laplacian plus scalar-potential expression near
  zero;
- `scalar_crit_tame` supplies the support-independent critical energy closure
  with top coefficient `23 / 12 < 2`;
- `galerkin_energy_uniform_bound_perScale` converts those differential
  inequalities into bounds uniform over all finite sets.

The initial bound is the full weighted spectral mass of
`ccTensorToHs q 0 k u0`; finite partial sums are bounded by its summable total.
No chart-selector hypothesis, extra convergence assumption, or frontier
wrapper is introduced.

## Verification and frontier

The focused Lean check passes without warnings or `sorry`.  Thus
`scalar_gal_bound` and its dedicated finite-dimensional energy machinery are
both **100% verified**.  The final performance repair was to isolate the finite
scalar-sum normal form in the private `gal_crit_nf`; this avoids rechecking the
same nested spectral expressions inside the already large assembly theorem and
does not change its assumptions or public interface.  The initial-energy step
uses the canonical low-layer finite-partial-mass bound
`cc_partial_le_norm`.

The next genuine analytic frontier is `scalar_gal_subseq`: extracting one
coefficientwise-uniform subsequence and inheriting every weighted-mass bound.
That theorem remains **0% verified** until its own source checks.  Its dedicated
compactness machinery is approximately **95% assembled**.  The later limit
identification and scalar strong-solution theorem remain **0% complete**, with
their dedicated machinery approximately **40% assembled**, before the separate
second-order bootstrap frontier.

## 2026-07-15 norm producer export

`galVec_norm_sq` is now a public canonical energy-layer theorem rather than a
private duplicate in the compactness consumer.  It gives the exact finite
weighted coefficient formula used for support-independent `H²` domination.
Focused verification passes without warnings or `sorry`; the exported object is
still being refreshed through the shared upstream build queue.

The theorem is infrastructure only.  Completion of the downstream
`scalar_gal_limit` remains recorded in `ConjGalerkinStrong.md` and is not counted
from this export by itself.
