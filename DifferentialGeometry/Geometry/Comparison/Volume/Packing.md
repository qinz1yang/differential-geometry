# Packing.lean

## 2026-07-08

Added `VolumeComparison.card_le_of_mul_lt`, the arithmetic endpoint for a
finite volume-packing proof.  If the measure part has already produced
`(n : Real) * L <= U` with `0 < L`, and the chosen integer cap satisfies
`U < (N + 1) * L`, then `n <= N`.

This deliberately does not prove a measure-theoretic disjoint-union estimate.
It isolates the final numeric gate needed by the future
`VolumeComparisonInput.ballMult` producer: the remaining frontier is to derive
the real inequality from lower bounds on pairwise disjoint small balls and an
upper bound on a containing ball.

Verification passed.  The module was also imported from `DifferentialGeometry.lean`
and the new module `.olean` was refreshed without the global Lake lock so the
root focused check could read it.

Added `VolumeComparison.mul_lower_le_upper`, the finite disjoint-measure bridge
feeding the arithmetic gate.  For a finite pairwise disjoint family of
measurable small sets contained in a large set, if each small set has real
measure at least `L`, then `(J.card : Real) * L <= μ.real large`.

The proof uses Mathlib's finite disjoint-union real-measure equality and real
measure monotonicity.  It intentionally stays at the abstract measure layer:
the remaining geometric frontier is to instantiate the small sets as balls,
prove the required disjointness/containment/measurability facts, and supply the
local lower and containing-ball upper volume bounds from the comparison
machinery.

Verification passed.  The focused file check, the explicit module `.olean`
refresh, and the root import focused check were all run without the global Lake
lock.

Added the metric-ball packing layer:

- `balls_disjoint`: radius `r / 2` balls around an `r`-separated finite family
  are pairwise disjoint.
- `balls_subset_ball`: if selected centers lie within `m * r` of `z`, the union
  of their radius `r / 2` balls is contained in the radius `(m + 1 / 2) * r`
  ball around `z`.
- `ball_mul_le`: combines those metric facts with `mul_lower_le_upper` to prove
  the cardinality-times-lower-real-measure estimate for metric balls.

This moves the packing bridge from abstract measurable sets to the ball family
shape used by `VolumeComparisonInput.ballMult`.  It still does not prove the
full input field: the remaining frontier is to combine checked local ENNReal
volume lower/upper estimates, convert them to the real-measure constants needed
by `ball_mul_le`, and then feed `card_le_of_mul_lt` to produce a concrete
`J.card <= Imult m`.

Verification passed.  The focused file check, explicit module `.olean` refresh,
and root import focused check were again run without the global Lake lock.

Strengthened the packing API so it no longer assumes a globally finite measure:
`mul_lower_le_upper` and `ball_mul_le` now require only that the containing set
or containing ball has finite measure.  This is the right shape for noncompact
Riemannian volume applications, where the local upper volume estimate supplies
finiteness of the containing ball.

Added `ball_card_le_of_vol`, the capped metric-ball cardinality gate.  It takes
ENNReal lower bounds on the radius `r / 2` small balls, an ENNReal upper bound
on the containing radius `(m + 1 / 2) * r` ball, a positive real lower constant
`L`, a nonnegative real upper constant `U`, and a strict cap
`U < (N + 1) * L`, then proves `J.card <= N`.

This is now the generic checked core for a future `ballMult` producer.  The
remaining frontier has moved to choosing constants from the local two-sided
volume theorem uniformly enough to define `Imult m` and `r0`.

Verification passed.  Focused file check, explicit module `.olean` refresh, and
root import focused check were run without the global Lake lock.

Added `ball_card_le_meas`, the explicit-measurability version of the capped
metric-ball cardinality gate.  This is needed in C4 applications where the
metric balls come from a supplied metric while the manifold still carries a
stored topology/measurable structure: the caller supplies measurability instead
of relying on a `[BorelSpace]` instance to pick the right topology.

`ball_card_le_of_vol` is now the Borel convenience wrapper around
`ball_card_le_meas`.

Verification passed.  The focused file check, explicit module `.olean` refresh,
and root import focused check were run without the global Lake lock.
