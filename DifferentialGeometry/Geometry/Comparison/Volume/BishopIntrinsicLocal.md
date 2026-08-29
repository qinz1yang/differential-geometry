# Intrinsic Jacobi comparison on a geodesic

## Role

`exists_intrMean_on` is the intrinsic-geodesic form consumed by Calabi distance
comparison.  It weakens the existing global Ricci hypothesis to the quadratic
Ricci lower bound along the single intrinsic geodesic segment used by the
Jacobi construction.

## Route

The zero transverse-dimension case remains algebraic.  In positive transverse
dimension the proof constructs the same orthonormal perpendicular frame and
intrinsic Jacobi fields as `exists_intrMean`, then invokes the checked
`curveMean_le_on` interval comparison.  No completeness or curvature
hypothesis beyond those already required by the intrinsic exponential API is
added.  The canonical source file is held by another lane, so this module uses
the existing public smoothness, perpendicularity, and Wronskian APIs and keeps
only the two small linear-independence arguments private here; it does not
modify or force-release that claim.

## Verification

Focused verification passed without warnings after the genuinely consumed
`BishopJacobiLocal` module was refreshed.  The first attempted proof exposed
five private upstream helpers; the final proof replaces three with public APIs
and keeps only the two short linear-independence arguments local.

## Next theorem

The next producer is a localized `exists_calabiData` whose Ricci input is
required only along the selected minimizing segment and its short Calabi tail.
