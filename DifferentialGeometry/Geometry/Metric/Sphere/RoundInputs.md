# RoundInputs

## Role

This module packages the two standard inputs needed when applying the positive
Killing--Hopf theorem to the three-sphere:

- `roundBundle` installs the tangent fibre inner product defined by
  `roundMetric`;
- `round_enorm` reads the resulting extended norm in the exact square-root
  form consumed by the intrinsic exponential API;
- `sphereBasisPt` supplies canonical coordinate points, with reusable
  non-equality and non-antipodality lemmas.

## Route

The extended-norm identity is not asserted for an arbitrary
`RiemannianBundle`.  It uses the existing tangent norm-diamond bridge only
after installing the bundle structure induced by `roundMetric`.  For
`EuclideanSpace ℝ (Fin 4)`, indices `0` and `1` give the required points:
`sphereBasisPt 0 ≠ sphereBasisPt 1` and
`sphereBasisPt 1 ≠ -sphereBasisPt 0`.

## Verification and progress

Focused verification and the exact module build passed.  The file is
warning-free and contains no `sorry` or `admit`.

This standard-round-sphere input subtask is complete (100%): the source
Riemannian bundle, exact `hRound` readout, and concrete non-antipodal
three-sphere points are all available.  The positive Killing--Hopf machinery
remains approximately 82% of the dedicated `ham3_space_box` infrastructure.
The theorem `ham3_space_box` itself remains unproved and is therefore 0%;
the quotient/deck-action endpoint assembly is still the substantive remaining
phase.
