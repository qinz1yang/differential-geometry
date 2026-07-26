# MapConvergenceDeriv

## 2026-07-15 canonical placement

The generic derivative and convergence-algebra closures were moved from the
HCG tree into `Analysis/Calculus` without renaming their public declarations.
The new `MapCInfConvOnCompacts.fderivOn` proves convergence of the full
Fréchet-derivative field on an open domain, consuming one additional derivative
order from the original family.

Focused verification passed. The old HCG file is now a compatibility import.

## 2026-07-16 fixed pullback contraction

Added the reusable Euclidean polynomial `pullbackForm`, its evaluation lemma,
and its global smoothness theorem.  The construction pulls a real-valued
continuous bilinear form back along a continuous linear map, so the composition
layer can combine an already-composed metric-coefficient field with an
`fderivOn` family in one ordinary smooth-composition step.

The smoothness proof adapts the established `bilinear_pullback_bundle_smooth`
route from `Geometry/Flow/RicciFlow/Pullback/Defs.lean`: two `clm_comp` steps
with the flip operation realized by a continuous linear isometry.  This avoids
duplicating the composition convergence machinery in the derivative layer and
also works for different source and target model spaces.  Focused verification
passed.
