# KillingHopf

## Role

This is the global positive Killing--Hopf producer needed before the
three-dimensional space-form quotient assembly.  It must construct a genuine
round-sphere diffeomorphism to a complete simply connected curvature-one
target and retain its metric-preserving differential.

## Current route

The theorem uses two one-pole `punctCartan` maps.  The second map is initialized
from the first map's value and differential at a second center.  Rigidity on
the sphere with the two excluded antipodes removed proves overlap agreement.
The maps are then glued, and compact-source covering theory upgrades the result
to a global diffeomorphism.

The source sphere metric world is now explicit: `sphere_diffeo_one` consumes
the caller-installed `PseudoEMetricSpace` and the `CompleteSpace` instance for
that pseudo-metric's induced uniformity.  It no longer silently asks for an
`IsRiemannianManifold` proof relative to the canonical chordal sphere metric.
This is internal plumbing for the round-cover producer, not a new
`ham3_space_box` consumer assumption.

## Verification and progress

Focused verification and exact module verification passed after the
metric-world parameterization.  The file contains no `sorry` or `admit`.

`ham3_space_box` remains unproved and is therefore 0%.  Its dedicated positive
Killing--Hopf machinery is approximately 82% complete:

- `punctCartan_match` constructs the aligned second initial isometry and proves
  equality of the two Cartan maps on their connected overlap;
- `sphere_diffeo_one` glues the maps, proves that the global map remains a
  local diffeomorphism and metric isometry, and upgrades it to a global
  diffeomorphism by compact covering theory;
- the global two-chart theorem in this file is 100%.

The remaining work toward `ham3_space_box` is no longer the positive
Killing--Hopf classification itself.  It is the endpoint integration: apply
this theorem to the curvature-one lifted metric on the universal cover, turn
deck transformations into an orthogonal finite-group action, and assemble the
round quotient model without hiding the universe and local-section seams.
