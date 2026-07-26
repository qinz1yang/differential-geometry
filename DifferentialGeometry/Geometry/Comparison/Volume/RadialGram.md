# RadialGram.lean

## 2026-07-17 radial Wronskian producer

Added `radial_wronsk_zero`.  On one common positive radial scale, two
packaged radial Jacobi fields whose launch directions are small have zero
Wronskian on every `Icc 0 b` with `0 < b < 1`.  The proof combines the existing
radial differentiability, interior and centre Jacobi equations, centre
vanishing, and the pointwise-regularity theorem `wronskian_zero_on`.

The proof body passed focused verification and the explicitly named module
build.  The declaration was then mechanically shortened from a 21-character
name to the project-compliant `radial_wronsk_zero`; a post-rename source check
was blocked by the active object refresh chain, whose next missing dependency
was `LeviCivita.Curvature.Realized.olean`.  No proof body changed during the
rename.  This is a radial symmetry producer, not a Bishop--Gromov theorem.

A follow-up API audit found that linear independence below the selected normal
radius is not a new no-conjugate-points theorem: `expMapDiffeo` already makes
its differential invertible on its source.  The remaining local bridge is the
scaling identity `J_{x,w}(t) = J_{t*x,t*w}(1)` and transport of that injectivity
to the radial family.  An attempted implementation was not retained because an
active upstream `.olean` refresh chain prevented verification.  The genuinely
geometric frontier begins with the shape operator and trace Riccati inequality
from the Ricci lower bound.  Polar integration and cut-locus transfer remain
later frontiers.

## 2026-07-19 polar density bridge

Added the public theorem `normalDensity_curve`.  Given a basis indexed by
`Option ι` whose `none` vector is the radial direction and whose `some` vectors
are perpendicular to it at the center, the theorem identifies
`r ^ card ι * normalChartDensity (r • u)` with a positive, radius-independent
constant times the transverse `curveDensity`.  It uses the existing exact
radial scaling identity, the Gauss lemma, a basis-change determinant, and
positivity of the normal and curve Gram matrices.  It adds no unit-speed,
orthonormal-frame, cut-time, or no-conjugate-points assumption.

Focused verification passed without warnings, and the explicitly named module
refresh completed successfully.  This closes the determinant
bridge selected by the local Route B ruling.  The next theorem is the routine
consumer `normalRatio_anti` in `BishopRadial.lean`.  Before radial integration,
the live polar theorem still needs a center-metric-ball version: its current
tangent ball uses the fixed ambient model norm, not the norm from `g.inner p`.

`normalDensity_curve` itself is complete (100%).  `normalRatio_anti` remains
unstated (0%; its dedicated inputs are about 90%).  The local relative-volume
and packing endpoints remain unstated (0%); their dedicated Route B machinery
is about 50%.  Global Bishop--Gromov and the producer from
`SeqBoundedGeometry` to the old arbitrary-center `VolumeComparisonInput`
remain 0%.  The full V1--V3 volume-comparison/CGT producer program is about
38--42% in machinery coverage; unconditional HCG compactness endpoints remain
0% as theorems.

## 2026-07-24 component-local radial Wronskian

Removed the stale `ConnectedSpace M` binder from `radial_wronsk_zero`.  Its
only endpoint input is `exists_radialJacobi_zero_radius`; all curves and fields
remain in the component of the chosen center, while completeness continues to
provide the intrinsic geodesics.

After the dependency-ordered refresh of `JacobiVariation` and
`NormalChartMeasure`, focused verification passed without diagnostics, and the
exported artifact refresh is GREEN.  No wrapper, replacement theorem, or
additional assumption was introduced.  The Wronskian producer remains
mathematically complete; the fixed-metric Calabi support theorem remains
unstated (0%).
