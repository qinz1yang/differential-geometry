# Small-time reduced-volume bounds

## Purpose

`redVolume_le_one` and `redVolume_zero_lim` are the global consumers of the
checked pointwise small-time chain.  The first rewrites reduced volume as the
source-domain integral, uses `lRedJac_le_gauss` on the strict minimizing
domain, enlarges that domain to the whole model space, and closes with
`lSrcGauss_mass`.

For the zero-time limit, the source-domain integral is written on the whole
model space using an indicator.  `lInj_eventually` gives eventual pointwise
membership in that domain, `lRedJac_tau_lim` gives the pointwise Gaussian
limit, and `lRedJac_le_gauss` supplies the integrable domination.  The source
Gaussian has total mass one, so dominated convergence yields
`redVolume_zero_lim` under only regularity of the terminal time.

The private continuity lemma `lRedPull_contOn` is proved from the existing
fixed-time partial L-exponential density theorem, parameter-density
continuity, and local smoothness of reduced length.  It introduces no new
public API.

## Status

Both public theorems are warning-free focused green without placeholders.
The module's targeted artifact refresh is green.

`redVolume_zero_lim` is **100%**.  Its dedicated pointwise and source-domain
exhaustion machinery is **100%**, and the reused generic dominated-convergence
and source-Gaussian infrastructure is **100%**.  This closes the small-time
reduced-volume normalization brick, but does not materially change the much
larger denominator: P2 remains below **1%**, and the whole Poincare program
remains approximately **3--5%**.
