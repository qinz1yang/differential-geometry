# BishopRadial notes

## 2026-07-18 assembled local radial producer

- Added `exists_radial_base` and `radialRatio_auto`, then assembled
  `exists_radial_cmp`. One common radius now supplies differentiability,
  Jacobi fields, linear independence, Wronskian symmetry, the mean comparison,
  and antitonicity of the local radial density ratio.
- The current honest producer retains completeness, connectedness, continuous
  Riemannian-bundle data, and the norm compatibility hypothesis because the
  available Wronskian/frame construction genuinely consumes them.
- Focused verification and the exported module refresh passed.
- This is local dedicated machinery only. The global Bishop--Gromov theorem
  and the `SeqBoundedGeometry` volume-input producer both remain 0% proved.

## 2026-07-19 normal-density ratio transfer

Added `normalRatio_anti`, the direct consumer of `normalDensity_curve`.  A
positive radius-independent basis factor multiplies the transverse
`curveDensity / hypDensity` ratio, so its antitonicity transfers to
`r ^ card ι * normalChartDensity (r • u) / hypDensity`.  The theorem carries
only the normal source/radius assumptions and the already-proved curve-ratio
input; it does not repeat the Riccati producer's geometric hypotheses.

Focused verification passed without warnings.  `normalRatio_anti` is complete
(100%).  The next substantial theorem `normalBall_ratio` remains unstated
(0%); before it can be stated honestly, the polar layer needs a center-metric-
ball adapter because the live formula uses the fixed ambient model norm.
Dedicated Route B machinery is about 52%, the full V1--V3 volume-comparison/CGT
program is about 39--43%, and unconditional HCG endpoint theorems remain 0%.

## 2026-07-24 component-local radial comparison

Removed the stale `ConnectedSpace M` binder from `exists_radial_cmp` and its
mean-curvature projection `exists_radial_mean`.  The only inherited use was
`radial_wronsk_zero`, whose canonical producer is now component-local; the
Riccati and Ricci-lower-bound arguments themselves were already local.

After the dependency-ordered refresh through `JacobiVariation`,
`NormalChartMeasure`, and `RadialGram`, focused verification passed without
diagnostics, and the exported artifact refresh is GREEN.  The independent
dimension-one case is not folded into these declarations: their existing
positive transverse-dimension premise is unchanged and the Calabi consumer
must handle the empty transverse family separately.  The comparison theorems
remain mathematically complete; `calabiDist_support` remains unstated (0%).
