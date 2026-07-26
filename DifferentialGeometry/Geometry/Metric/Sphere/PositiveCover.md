# PositiveCover

## Role

This module applies the positive Killing--Hopf theorem to the normalized lifted
metric on a universal cover.  It owns the metric-instance, norm-identity, and
completeness setup and retains the differential isometry equation needed to
conjugate deck transformations to round isometries.

## Current route

`sphereCover_one` scales a positive constant-curvature metric to curvature one,
installs its Riemannian distance on the compact base, pulls completeness to the
universal cover, and applies `sphere_diffeo_one` using the exact lifted
curvature formula.  On the source sphere it likewise installs the distance
induced by `roundMetric` and pins completeness to that pseudo-metric's exact
uniformity; this avoids silently falling back to the canonical chordal
uniformity.

## Project position

Focused verification and the exact module build passed.  The file is
warning-free and contains no textual `sorry` or `admit`.  The former
`fibre_countable` dependency found by the first audit is now replaced by the
refined polygon-code proof.  The downstream exact replay passes, and
`sphereCover_one` and the related universal-cover producers have axiom audits
containing only `propext`, `Classical.choice`, and `Quot.sound`.

`sphereCover_one`, `ham3_space_box`, and their dedicated positive-space-form
machinery are complete and trusted (100%).  The whole HCG infrastructure
remains conservatively about 60%.
