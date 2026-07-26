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

The downstream `scalar_gal_limit` theorem is now **100% verified** in
`ConjGalerkinStrong.lean`: it passes the finite ODE integral identity to the
limit and constructs the spectral strong solution.  The classical moving
conjugate-heat theorem and both Perelman/Hamilton noncollapsing endpoints remain
**0%**; this file itself advances only their analytic machinery.

## Next spectral limit producer

The post-subsequence fixed-time producers `galLimHs` and `galLim_tendsto` are
also **100% verified**.  They package `ulim t` as an `H^m` element using
`lim_mass`, construct the difference at order `m+1`, and use the public
`tendsto_of_coeff` at the strict downshift `m < m+1`.  Modewise convergence
comes from `conv`, the high-order norm bounds come from `energy` and
`lim_mass`, and eventual membership comes from the strictly monotone spectral
exhaustion.  No new convergence predicate or consumer assumption is used.

The next frontier is now the bridge from the all-order spectral strong path to
joint spacetime smoothness and `IsHeatPotOn`; the present intrinsic
partition-of-unity all-order completeness theorem is not yet that realization
bridge.

Honest accounting: `scalar_gal_subseq` and `galLim_tendsto` are theorem-level
**100% verified**.  `scalar_gal_limit` and its dedicated machinery are also
**100% verified**.  `heatpot_of_maxreg`, the classical moving conjugate-heat
theorem, and both noncollapsing endpoints remain theorem-level **0%**.

## 2026-07-15 strong-limit handoff preparation

`IsConjGalSubseq` now retains continuity of the already-constructed moving
perturbation as producer data, and `scalar_gal_subseq` fills that field from the
existing A2/A1 continuity theorems.  This is not a new consumer assumption.
`galLimPath` and `galLimPath_cont` package the all-order coefficient limit as a
continuous Sobolev path by using one higher uniform mass bound and
`cont_of_coeff`.

Focused verification of these additions now passes without warnings or
`sorry`.  The temporary `galVec_sq` compatibility copy has been deleted, and
both consumers use the canonical public `ConjGalerkinEnergy.galVec_norm_sq`.
The existing large `scalar_gal_subseq` assembly needs a declaration-local 800k
heartbeat budget after retaining `pert_cont`; this changes neither its statement
nor any global option or consumer assumption.

The downstream `ConjGalerkinStrong.scalar_gal_limit` closure now passes focused
verification and module export without `sorry`; the theorem and its dedicated
machinery are **100%**.  The next exact frontier is the separate joint-spacetime
realization bridge to a classical `IsHeatPotOn` solution.

## 2026-07-19 exact compactness interval

`gal_subseq_on` separates compactness from lifetime selection.  It consumes
exact-interval energy data and continuity of the full `scalarGalPert`, then
returns `IsConjGalSubseq` on precisely that interval.  Compactness of the time
interval supplies a single perturbation norm bound through `galPert_bdd_on`, so
the old private A2/A1 split estimate is removed.  `scalar_gal_subseq` keeps its
public statement and is now a compatibility wrapper which performs the legacy
shortening once before calling the exact engine.

No downstream assumption or new convergence predicate was added.  The source
contains no local `sorry`; focused verification is pending the active upstream
spectral object refresh.  Therefore `gal_subseq_on` remains theorem-level
**0%**, with approximately **98%** dedicated source machinery, until its own
file check passes.

## 2026-07-23 post-merge check

The limit wrapper now uses ordinary `dsimp` at the two let-binder exposure
points before applying `gal_subseq_on`.  Focused verification and the module
artifact refresh both passed.
