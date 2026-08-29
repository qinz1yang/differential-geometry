# ActionMinC1

## Purpose

`lMinCurve_c1` upgrades a globally fixed-endpoint minimizing continuous curve
from a monotone finite chart-`H¹` realization to `C¹` regularity on the full
nondegenerate closed parameter interval.

## Route

The theorem first applies `exists_lStrict`, which removes zero-length pieces
while retaining the chart centers and dependent `timeH1` witnesses.  The
strict realization has at least one piece because otherwise its preserved
first and last nodes would force the distinct endpoints to agree.  The result
then follows directly from `lFinCurve_c1`; no separate one-piece or
multiple-piece consumer is needed here.

## Verification and progress

Focused verification passed without warnings or placeholders.  This theorem is
the canonical bridge from relaxed finite attainment data to full `C¹`
regularity.  `lMinCurve_c1` and this bridge are 100% complete.  They are
dedicated minimizer-regularity machinery, not `exists_lMinimizer` or
`redVolume_anti`; those endpoints remain 0% until their declarations are
proved.  Dedicated L-geometry machinery is approximately 96--97%, while P2
remains below 1% and the whole Poincare program remains approximately 3--5%.

The focused noncompact recheck also passed without warnings. `lMinCurve_c1`
now exports without an ambient `CompactSpace M` instance; its refreshed export
for the complete-flow endpoint also passed.
