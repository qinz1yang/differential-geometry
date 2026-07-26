# StepCStageMaster

## Status

`stageMapCast` and `HasRadiusTail.geom_tail` contain no `sorry`.  Their source
is semantically framed-clean, and focused Lean verification passes against the
exact-refreshed Injectivity and Diagonal imports.  This module's own exact
target refresh also completed successfully in the coordinated write chain.
This closes the purely index-theoretic transport from a fixed integer-radius
tail to the master sequence for the first three concrete Step-B1 fields.

## Implemented route

- `stageMapCast` transports only the source and target manifold indices of the
  actual finite-stage comparison map.
- `HasRadiusTail.geom_tail` keeps the radius-tail selector, its strictness, the
  exact tail/master index equality, and the corresponding `HasStageJetData`.
- One shifted threshold then gives, for every pair of sufficiently large
  master indices, local diffeomorphism and injectivity on the retained closed
  source ball together with exact basepoint preservation for the same
  transported map.
- No `LiveSlot` or `InterSlot` equivalence is introduced.  All branch-local
  types remain attached to the fixed-radius tail where they were constructed.

The equality transport is isolated in a private generic lemma.  This avoids
dependent elimination on expressions such as `psi k`, which was the only local
Lean obstruction encountered while assembling the theorem.

## Remaining frontier and accounting

The master-sequence transport in this file is complete (100% current module
verification).  The forward and exact-inverse intrinsic metric bridges and
the concrete `MetricCompactBase.exists_b1_raw` proof body are now implemented;
their canonical framed dependency chain has not yet been revalidated, so they
must not be reported as framed-green.  The separately named textbook Step B1
theorem remains unstated/unproved (0%).  Rounded dedicated Step-B/B1 machinery
is about 95%, Chapter 4 machinery about 87%, and whole-HCG machinery about 60%.
