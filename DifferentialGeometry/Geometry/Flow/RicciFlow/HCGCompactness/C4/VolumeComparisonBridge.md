# VolumeComparisonBridge.lean

## 2026-07-08

Added `exists_pairR_of_boundedGeometry`, the C4/HCG application-layer bridge
from a pointed metric object with `MetricComplete`, connectedness, and
`BoundedGeometry` to the comparison-layer small-ball two-sided volume estimate.
The theorem consumes `VolumeComparison.exists_pairR_bound` and supplies its
remaining curvature input via `rm04Bound_of_geom`.

Layering decision: keep this bridge in `C4/`, not in `BoundedGeometry.lean`,
because it needs the pointed-manifold metric-space and tangent-enorm setup in
addition to curvature boundedness.  `BoundedGeometry.lean` remains the curvature
producer layer.

Important instance lesson: the Riemannian fiber instances used by Hopf--Rinow
are scoped under `Bundle`; this file must use `open scoped Bundle`.  Also avoid
exposing an explicit `letI : IsContinuousRiemannianBundle ... := inferInstance`
in the theorem return type.  Instead install
`cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : Y.M -> Type _)` and
the `RiemannianBundle` from `cg.toRiemannianMetric`; the continuous-bundle
instance is then inferred at the consumer call sites.

Verification passed.  The only tooling wrinkle was stale upstream `.olean`
state after adding new declarations to `BallVolume.lean` and
`BoundedGeometry.lean`; the explicitly named upstream modules were refreshed
without the global Lake lock.

Next target: decide whether to build the packing/multiplicity producer that
turns the local small-ball volume estimate into `StepAInputs.VolumeComparisonInput`,
or first add a sequence-level wrapper applying `exists_pairR_of_boundedGeometry`
to every term of a `PointedRiemannianSeq`.

## 2026-07-08 follow-up

Added `exists_pairR_of_seqBoundedGeometry`, the sequence-level wrapper applying
the pointed local-volume bridge to `X.obj k`.  Inputs are
`SeqMetricComplete`, per-member connectedness, and `SeqBoundedGeometry`; the
proof packages the `k`th `SeqBoundedGeometry` fields into a local
`BoundedGeometry` record and reuses `exists_pairR_of_boundedGeometry`.

Verification passed.  This does not prove `StepAInputs.VolumeComparisonInput`:
that target is still a packing/multiplicity theorem, and the remaining bridge
needs a disjoint small-ball volume-count argument or an explicit book-external
Bishop--Gromov packing producer.  Current useful output is only the per-sequence
small-ball two-sided volume estimate under bounded geometry.

Next target: either state the exact intermediate packing lemma needed to turn
lower bounds on disjoint small balls plus an upper bound on the containing ball
into `J.card <= Imult m`, or keep `VolumeComparisonInput` as a documented
book-external input and wire `exists_pairR_of_seqBoundedGeometry` only into the
future producer note.

## 2026-07-08 follow-up: packing producer feasibility

`Volume/Packing.lean` now supplies the checked generic packing core through
`ball_card_le_of_vol`: ENNReal small-ball lower bounds plus an ENNReal
containing-ball upper bound imply the natural-number cap.

Attempting to turn `exists_pairR_of_seqBoundedGeometry` directly into
`VolumeComparisonInput.ballMult` exposes a real uniformity obstruction.  The
current local volume theorem chooses its constants after the center point `p`:
`C`, `D`, `Blo`, `A`, and the smallness radius ultimately depend on pointwise
normal-coordinate data such as `gpCoerciveConst g p` and
`exists_basis_upper_const g p`.  `SeqBoundedGeometry` only supplies uniform
curvature-derivative bounds; it does not currently supply a uniform lower bound
for those normal-coordinate radii/constants across all centers and all sequence
members.

So the checked local two-sided ball-volume bridge is not yet a producer of the
book's A0' field.  The next honest step is one of:

- add a real Bishop--Gromov relative volume/packing theorem under the Ricci
  lower-bound hypotheses, which is the book-faithful source of `ballMult`; or
- add an explicit uniform local-volume-comparison input carrying constants and
  a radius `r0` uniform in `k` and center, then consume
  `ball_card_le_of_vol`.

Verification status: no new Lean theorem was added in this bridge file during
this feasibility pass; the blocker is missing uniform comparison API, not a
local proof failure.

## 2026-07-08 follow-up: explicit uniform input producer

Added `UniformBallPack`, an explicit uniform local-volume packing input.  It
carries:

- the Step A distance and a concrete metric realizing the metric balls;
- a uniform radius cap `r0` and multiplicity function `Imult`;
- uniform lower and upper constants `L m r` and `U m r`;
- a strict numeric cap `U m r < (Imult m + 1) * L m r`;
- small-ball measurability plus ENNReal lower and upper volume estimates,
  uniform in `k` and center.

Added `UniformBallPack.toVCInput`, which converts this input into
`StepAInputs.VolumeComparisonInput` by applying the checked packing core
`VolumeComparison.ball_card_le_meas`.

This does not discharge Bishop--Gromov from `SeqBoundedGeometry`; it makes the
missing uniform comparison hypothesis explicit and gives a verified consumer
path once that hypothesis is supplied.

Verification passed.  The focused check and targeted module build were run
without the global Lake lock.
