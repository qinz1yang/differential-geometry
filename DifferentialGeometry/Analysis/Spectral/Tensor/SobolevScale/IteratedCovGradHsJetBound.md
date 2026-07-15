# Iterated covariant-gradient spectral jet bounds

## 2026-07-13 rank-generic spectral bridge

The previous public jet-to-spectral theorem was restricted to
`SmoothCcTensor g₀ 0 2`.  The first generalization attempt exposed the actual
lower-layer issue: both `smoothCcToTensorHs` and `ccSpectralEmbed` were themselves
rank-two constructors, even though the eigen-coordinate, rough-Laplacian,
Gårding, and commutator engines underneath them were already rank-generic.

This file now provides the generic smooth spectral embedding
`ccTensorToHs g₀ s σ`, its coefficient formula, weighted-norm formula, and
order monotonicity.  It also proves both directions of the finite-order norm
comparison for every covariant rank:

- `hsJet_le`: the covariant `L²` jet through order `n` is bounded by the
  spectral `H^n` norm;
- `hs_le_jet`: the spectral `H^n` norm is bounded by that covariant jet.
- `ccGrad_le`: applying `j` covariant derivatives shifts the spectral order by
  `j`, with a rank- and order-dependent constant.

The old rank-two theorem
`exists_iteratedCovGrad_sum_le_smoothCcToTensorHs` remains available as the
`s = 2` compatibility specialization.  The generic forward proof reuses the
existing all-order Gårding and rough-Laplacian commutator estimates.  The reverse
proof uses the even/odd spectral mode identities and the two-mode estimate
`(1 + λ)^n ≤ 2^(n-1) (1 + λ^n)`, avoiding a duplicated all-modes binomial
proof.

The derivative-shift corollary is deliberately only an assembly theorem.  It
applies `hs_le_jet` to the differentiated tensor, uses composition of iterated
covariant gradients to place the resulting finite jet inside the source jet,
and closes with `hsJet_le`.  It introduces no additional analytic estimate or
consumer hypothesis.

Two local failures were informative rather than mathematical blockers.  The
initial statement could not elaborate against the rank-two-only embedding, so
the generic embedding was added at this Sobolev-scale layer.  The final reverse
proof then needed the namespaced `Summable.tsum_add`; after that repair focused
verification passed, including `ccGrad_le`.  No consumer assumption,
chart-selector hypothesis, or new geometric hypothesis was introduced.

The target `.olean` refresh was not completed in this shared worktree.  Although
the source passed focused verification, changing upstream timestamps repeatedly
expanded the named refresh into a broad rebuild.  No current downstream check
needed the newly exported declarations, so focused GREEN was accepted and the
owned refresh was stopped without touching another lane.

Honest accounting: `hsJet_le` and `hs_le_jet` are theorem-level 100%.  The
target `scalar_crit_tame` theorem is still unstated/unproved (0%); its dedicated
machinery is roughly 55%, and this closed spectral-jet dependency is only about
10--15% of that proof.  Perelman's no-local-collapsing producer and
`ham3_noncollapse` remain theorem-level 0%; their dedicated analytic machinery
is about 40%.  Whole HCG machinery remains about 53%, while the HCG endpoint
theorems remain 0%.

## 2026-07-14 finite partial spectral mass

`cc_partial_le_norm` is the canonical rank-generic estimate that every finite
weighted coefficient mass of a smooth compactly supported covariant tensor is
bounded by its full spectral Sobolev norm squared.  The proof stays in the
spectral producer layer: rewrite the norm by `ccToHs_norm_sq`, then use
nonnegativity and weighted summability.  This avoids making Ricci-flow consumers
re-elaborate `sum_le_tsum` through the full moving-geometry import environment.

Focused verification passed without local warnings or `sorry`.  The theorem and
its dedicated machinery are 100%.  `scalar_crit_tame` is now independently
verified (100%).  `scalar_gal_bound` remains theorem-level 0% until its own
focused check passes, although its dedicated machinery is approximately 99%.
The classical moving conjugate-heat theorem and both Perelman/Hamilton
noncollapsing endpoints remain theorem-level 0%.
