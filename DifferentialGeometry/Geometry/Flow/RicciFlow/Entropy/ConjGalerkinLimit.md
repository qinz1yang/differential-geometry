# Scalar conjugate-heat Galerkin compactness

## Role

`ConjGalerkinLimit.lean` is the compactness producer between the uniform finite
Galerkin energy theorem and the later identification of the limiting
coefficients with a spectral mild/strong solution.

The output predicate `IsConjGalSubseq` keeps the actual finite-dimensional ODE,
initial coefficients, off-truncation support, and all-order energy bounds.  It
also records one strictly monotone subsequence, modewise uniform convergence on
the common time interval, continuity of every limiting mode, the exact initial
coefficients, and inherited all-order weighted mass bounds.  This is not a
frontier wrapper: `scalar_gal_subseq` constructs every field from
`scalar_gal_bound`, the genuine operator bounds, and the generic compactness
producers.

## Proof route

The truncations are the rank-generic `eigenFinset` exhaustion.  Order-zero
energy bounds each scalar coefficient.  Order-two energy bounds the finite
`H²` vector, while `lapDiffA20_short` and `conjA1_short` bound the perturbation
operator.  The finite ODE therefore gives a support-independent, modewise
right-derivative bound.  `right_lipschitz` converts it to equi-Lipschitz control,
and `galerkin_subseq` extracts one subsequence uniformly in every countable
mode.  `fatou_sq_mass` passes each all-order energy bound to the limit.

No HCG compactness module, Aubin–Lions theorem, intrinsic Rellich `sorry`, chart
selector, or additional consumer assumption is used.

## Verification and frontier

The complete file passes focused verification without warnings or `sorry`.
Therefore `scalar_gal_subseq` and its dedicated compactness machinery are both
**100% verified**.  The cumulative-heartbeat repair isolates four independent
private producers: `galPert_norm_le`, `gal_lim_mass`, `gal_lim_init`, and
`supp_right_lip`.  The public theorem and its assumptions are unchanged.

The next theorem, tentatively `scalar_gal_limit`, remains **0%**.  It must pass
the finite ODE integral identity to the limit and construct the spectral
mild/strong solution.  The classical moving conjugate-heat theorem and both
Perelman/Hamilton noncollapsing endpoints remain **0%**; this file advances only
their analytic machinery.

## Next spectral limit producer

The post-subsequence fixed-time producers `galLimHs` and `galLim_tendsto` are
also **100% verified**.  They package `ulim t` as an `H^m` element using
`lim_mass`, construct the difference at order `m+1`, and use the public
`tendsto_of_coeff` at the strict downshift `m < m+1`.  Modewise convergence
comes from `conv`, the high-order norm bounds come from `energy` and
`lim_mass`, and eventual membership comes from the strictly monotone spectral
exhaustion.  No new convergence predicate or consumer assumption is used.

The next frontier `scalar_gal_limit` must pass the finite right-derivative ODE
to an interval-integral identity by dominated convergence and package the
result in the existing `timeL2` / `timeH1` interfaces.  The genuine later
frontier is the bridge from the all-order spectral strong limit to joint
spacetime smoothness and `IsHeatPotOn`; the present intrinsic
partition-of-unity all-order completeness theorem is not yet that realization
bridge.

Honest accounting: `scalar_gal_subseq` and `galLim_tendsto` are theorem-level
**100% verified**.  `scalar_gal_limit` is unstated/unproved (**0%**) with
roughly **40%** dedicated machinery.  `heatpot_of_maxreg`, the classical moving
conjugate-heat theorem,
and both noncollapsing endpoints remain theorem-level 0%.

## 2026-07-15 strong-limit handoff preparation

`IsConjGalSubseq` now retains continuity of the already-constructed moving
perturbation as producer data, and `scalar_gal_subseq` fills that field from the
existing A2/A1 continuity theorems.  This is not a new consumer assumption.
`galLimPath` and `galLimPath_cont` package the all-order coefficient limit as a
continuous Sobolev path by using one higher uniform mass bound and
`cont_of_coeff`.

Focused verification of these additions is currently blocked before the proof
body by the shared target build refreshing a long chain of missing upstream
objects.  A private `galVec_sq` copy is temporarily present only so this file can
be checked before the newly public `ConjGalerkinEnergy.galVec_norm_sq` object is
available; it must be removed and both call sites restored to the canonical
producer before this change is treated as complete.

The exact downstream frontier is `ConjGalerkinStrong.scalar_gal_limit`.  Its
source now contains the scalar DCT, vector FTC, and `timeH1` packaging, but the
theorem remains **0% verified** until the focused check succeeds.
