# `DeTurckRicciPde` status

## 2026-07-13 short-time-existence branch alignment

The default project build exposed a duplicate declaration of
`deturck_ricci_flow_parabolic_short_time_existence`: this file still contained
an unused, deferred (`sorry`) endpoint while
`DeTurckInitialDataExistence.lean` exports the canonical proved producer under
that name.  Importing both modules made the root `DifferentialGeometry.lean`
environment fail before elaboration.

The unused duplicate endpoint was removed rather than renamed into a second
public frontier.  This file retains the realized interior/initial-time
DeTurck--Ricci PDE lemmas; the canonical existence API remains in
`DeTurckInitialDataExistence.lean`.  No consumer used the removed declaration,
and the headline short-time theorem already consumes the proved construction
route.

Focused verification, the targeted module refresh, and the default root project
build passed.  The short-time-existence theorem remains proved (100%); its
dedicated machinery and default-root integration are 100%.  Merge preparation
is 100%, and the merge commit carrying this note completes the branch alignment
(100%).  Hamilton positive-Ricci and HCG compactness theorem completion are
unchanged.
