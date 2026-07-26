# HarmonicDensityReg status

## Source facts

`hmfSpecMap_cd` first exposes the target component of the diagonal exponential
as a jointly smooth coefficient/spatial map.  `hmfSpecSlice_cd` then extracts
a genuine whole-manifold `C^n` self-map for every
coefficient in the finite-spectral local-addition ball already supplied by
`hmfSpecAdd_cd`.  Its radius is uniform in the manifold point and is not
misstated as uniform in the spectral cutoff.

`hmfSpecTan_cd` applies the manifold tangent-map regularity theorem to those
actual slices.  Hence the spatial derivative entering `hmfDirDensity` is a
derived bundled tangent map, rather than an independent or total-`mfderiv`
placeholder.

The source contains no proof placeholder or additional analytic hypothesis.
Focused verification is pending the coordinated shared build lane.

## Remaining boundary

The next theorem must retain joint coefficient/spatial regularity of the
pure-spatial tangent-map evaluation, combine it with the smooth frames and
target metric, and identify the resulting scalar with `hmfDirDensity`.  It
then feeds compact parametric integration and the moving-volume continuity
theorems used by `hmfSpecResid`.

This is finite-mode local-addition machinery only.  Cutoff-uniform tame
estimates, Galerkin compactness, the common harmonic-map gauge, and the exact
`ricci_flow_forward_unique` theorem remain unproved; the endpoint is **0%**.
