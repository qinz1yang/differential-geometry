# RicciContinuityInMetricTime — notes

## 2026-07-17 — noncompact joint-curvature API

The joint chart Gram/Ricci/Riemann/scalar continuity chain did not use compactness, but the file-level
`[CompactSpace M]` variable leaked into the private joint-jet helpers and four public readouts.  The
canonical chain now explicitly omits that instance, including the local second-partial identity needed
by the joint two-jet proof.  No theorem was duplicated and no new hypothesis was introduced.

Focused verification and the exact module refresh passed.  This is a completed API correction (100%);
it changes no HCG endpoint theorem percentage by itself.
