# ActionC1

## Role

`lRegLag_int_c1` discharges regularized-action integrability for a `C¹` curve
on a compact parameter interval. It uses a finite preferred-chart subdivision,
canonical shifted `chartTimeH1` representatives for the kinetic term, and the
existing scalar-curvature continuity theorem. It does not assume that the
manifold is compact.

## Verification and progress

Focused verification passed without warnings. The file contains no `sorry`,
`admit`, or axiomatic placeholder.

The theorem itself is implemented. It closes the C¹ action-integrability
adapter, a small assembly step in the direct-method/minimizer phase. The
minimizer endpoint remains 0%, while its dedicated machinery is approximately
86% complete. `redVolume_anti` remains 0%; dedicated L-geometry machinery is
approximately 30%, reusable generic infrastructure for this lane approximately
60%, P2 remains below 2%, and the whole Poincaré program remains approximately
3–5%.
