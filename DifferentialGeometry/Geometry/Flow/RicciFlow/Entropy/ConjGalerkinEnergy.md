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

The downstream `scalar_gal_subseq`, `galLim_tendsto`, and `scalar_gal_limit`
theorems now all pass their own focused verification and are theorem-level
**100%** in their respective modules.  Those downstream closures are not
counted as completion of this finite-dimensional energy producer.

## 2026-07-15 norm producer export

`galVec_norm_sq` is now a public canonical energy-layer theorem rather than a
private duplicate in the compactness consumer.  It gives the exact finite
weighted coefficient formula used for support-independent `H²` domination.
Focused verification passes without warnings or `sorry`; the exported theorem
is now available to downstream modules.  `ConjGalerkinLimit` has removed its
temporary duplicate and uses this canonical producer directly.

The theorem is infrastructure only.  Downstream `scalar_gal_limit` completion is
recorded in `ConjGalerkinStrong.md` as theorem-level **100%** with **100%**
dedicated machinery, and is not counted from this export by itself.

## 2026-07-19 exact energy interval

`gal_bound_on` factors the energy hierarchy from lifetime selection.  It takes
an exact `IsConjGalTime` interval, the support-independent critical estimate,
and the moving-Laplacian finite-core equality on that same interval.  Its proof
reuses the existing `gal_crit_nf` and all-order energy theorem.  The public
`scalar_gal_bound` statement is unchanged and now selects its old short
interval before calling the exact engine.

This removes the target route's former `delta / 2` shrink: the new engine calls
`galPert_fin_of` pointwise from the supplied core equality.  No new regularity,
chart, convergence, or spectral-support assumption was introduced.  The source
contains no local `sorry`; focused verification is pending the active upstream
spectral object refresh, so `gal_bound_on` is theorem-level **0%** with about
**98%** dedicated source machinery until it elaborates.
