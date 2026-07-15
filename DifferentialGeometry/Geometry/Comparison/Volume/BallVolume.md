# BallVolume

## 2026-07-07 V1d upper-bound shell

Status: `BallVolume.lean` starts the V1d layer without claiming that the
geodesic-ball containment or Gronwall estimates are already proved.

Completed:

- Added `vol_le_ball_of_len`: if a measurable set lies in a normal-coordinate
  source, its normal-coordinate image is inside the Jacobi-valid radius and a
  model ball, and the endpoint radial Jacobi fields satisfy a uniform length
  bound there, then the Riemannian volume is bounded by the V1c density constant
  times the model-Haar measure of that model ball.
- Added `vol_le_ball_of_len_radius`: the same upper shell with the
  Jacobi-valid radius containment derived from `R <= expMapC2Radius`.
- Added `coordBall_vol_le`: the V1d upper shell specialized to the
  normal-coordinate image of a model ball, keeping measurability, chart-target
  containment, and endpoint Jacobi length control explicit.
- Added `coordBall_meas`: a model ball contained in the normal-chart target has
  measurable inverse normal-coordinate image.
- Added `coordBall_vol_le_tgt`: the coordinate-ball upper shell with
  measurability discharged from the chart-target containment hypothesis.
- Added `modelHaar_ball`: the positive-radius model-Haar ball scaling bridge
  from Mathlib's additive Haar ball formula.
- Added `coordBall_vol_scale`: the target-contained coordinate-ball upper
  bound with the model-ball measure rewritten as `R^n` times the unit model-ball
  measure.
- Added `ball_tgt_of_radius`: a small C2-radius projection showing that a
  model ball with `R <= expMapC2Radius` lies in the normal-chart target.
- Added `coordBall_vol_scale_c2`: the scaled coordinate-ball upper bound with
  chart-target containment discharged by `ball_tgt_of_radius`.
- Added `vol_ge_of_density`: a V1d lower-bound shell from a pointwise
  normal-coordinate density lower bound on the chart image.
- Added `coordBall_vol_ge` and `coordBall_vol_ge_sc`: coordinate-ball lower
  bounds, including the scaled `R^n` form, from a density lower bound.
- Added `coordBall_vol_ge_sc_c2`: the scaled coordinate-ball lower bound with
  chart-target containment discharged by `ball_tgt_of_radius`.
- Added `metricBall_vol_le` and `metricBall_vol_scale`: metric-ball upper
  consumers under explicit measurability, normal-chart source containment,
  normal-coordinate model-ball containment, and radial Jacobi length control.
- Added `metricBall_vol_ge`, `metricBall_vol_ge_sc`, and
  `metricBall_vol_ge_sc_c2`: metric-ball lower consumers from a contained
  coordinate ball and a density lower bound, including scaled and C2-discharged
  forms.
- Added `coordBall_subset_smallNormalBall_of_agree` and
  `exists_coordBall_subset_smallNormalBall`: a V1d lower-containment producer
  from normal-chart inverse points to the intrinsic Riemannian-distance ball,
  using local `expMapIntrinsic = expMap` agreement and
  `smallNormalBall_radial_confined`.
- Added `smallNormalBall_vol_ge_sc`, `smallNormalBall_vol_ge_sc_c2`, and
  `exists_smallNormalBall_vol_ge_sc`: scaled lower-volume consumers for
  intrinsic Riemannian-distance balls, packaged with the local agreement radius.
- Added `smallNormalBall_subset_metricBall` and
  `metricBall_subset_smallNormalBall`: realized `Metric.ball` bridges for the
  Hopf-Rinow Riemannian metric-space instance.
- Added `metricBall_meas`: realized Hopf-Rinow metric balls are measurable for
  the Borel structure used by the Riemannian volume measure.
- Added `exists_metricBall_vol_ge_sc_local`: a packaged local lower-volume
  theorem for realized metric balls, still conditional on the local radius,
  agreement, and density hypotheses.
- Added `metricBall_chartCtrl`: a local upper-containment producer for realized
  metric balls.  It uses Hopf-Rinow minimizing vectors, the local
  `expMapIntrinsic = expMap` radius, `expRadiusGp`, and coercivity of `g_p` to
  show that a small `Metric.ball p s` lies in the normal-chart source and has
  normal coordinates in `Metric.ball 0 R`.
- Added `exists_metricBall_vol_scale_local`: a packaged local upper-volume
  theorem for realized metric balls, still conditional on ball measurability
  and the V1c radial-Jacobi endpoint-length bound.
- Added `vol_le_ball_of_density`, `metricBall_vol_scale_density`, and
  `exists_metricBall_vol_le_dens_local`: upper-volume consumers from a
  pointwise normal-density upper bound, matching the lower-density interface.
- Added `exists_vol_two_dens`: a local two-sided realized metric-ball theorem
  whose V1c inputs are pointwise lower and upper density bounds on the same
  model ball.
- Added `exists_vol_two_rm04`: a local two-sided realized metric-ball theorem
  consuming `JacobianBounds.exists_dens_two_rm04`, while keeping the
  pointwise parallel-frame, scalar-model, curvature, launch, and radius
  hypotheses explicit.
- Added `Rm04FrameData`, `IsRm04VolHyp`, and `exists_vol_rm04_pkg`.  These
  split the remaining Rm04 local-volume input into explicit frame data and a
  proof predicate, then consume that package in the existing two-sided local
  volume theorem.
- Added `exists_rm04_scale` and `exists_vol_scale`.  These choose the common
  positive scale from `basisUnitScaleSmall`, fill only the scale fields of
  `IsRm04VolHyp`, and then consume the packaged local Rm04 volume theorem.
  All non-scale geometric fields remain explicit.
- Added `exists_metricBall_vol_two_local`: a local two-sided V1d assembly shell
  combining the lower and upper realized-metric-ball packages under one common
  smallness radius.  It still leaves the density lower bound, ball
  measurability, and radial-Jacobi endpoint-length bound explicit.
- Added `exists_vol_two_same`: the single-model-radius specialization of the
  local two-sided assembly theorem.  It is closer to the final capped-scale
  statement because both sides use the same model radius `R`, but the V1c
  density and radial-Jacobi inputs remain explicit.
- Added `exists_vol_two_meas`: the single-model-radius local two-sided theorem
  with metric-ball measurability discharged by `metricBall_meas`.  The V1c
  density and radial-Jacobi inputs remain explicit.

Route:

- This is only a measure-monotonicity wrapper over
  `normalChart_volume_le_const_mul_of_radial_length_bound`.
- It intentionally keeps the two hard inputs explicit: the normal-coordinate
  image containment in a model ball and the radial Jacobi endpoint length
  estimate.
- The radius-capped wrapper removes one bookkeeping hypothesis once the model
  ball radius is chosen below the local exponential C2 radius.
- The coordinate-ball wrapper uses only normal-chart inverse laws; it is the
  closest current statement to an integrated upper ball estimate without
  proving manifold metric-ball containment.
- The target-containment wrapper uses only the openness of the inverse
  partial-homeomorphism image; it still keeps chart-target containment and the
  radial Jacobi endpoint length bound explicit.
- The scaled wrappers use only `modelHaar_ball`; they do not prove any new
  geometric containment or Jacobi estimates.
- The C2 target wrapper uses `ball_subset_normalChartAt_target`; it is a
  bookkeeping projection from the existing exponential-coordinate radius, not a
  new injectivity or metric-ball theorem.
- The lower shells use `normalChart_volume_eq` plus monotonicity of the
  lower Lebesgue integral.  A local rewrite failure occurred because Lean
  unfolded the coerced `normalChartAt` map to `expMapDiffeo.symm`; the checked
  proof fixes this by changing the goal back to the named `φ '' (φ.symm ''
  ball)` shape before rewriting the image equality.
- `metricBall_vol_le` keeps metric-ball measurability explicit as a reusable
  lower-level consumer, while `metricBall_meas` discharges that premise for the
  Hopf-Rinow metric-space instance in the packaged local theorem.
- The metric-ball lower consumers use `coordBall_vol_ge` plus measure
  monotonicity.  They still leave the genuine geometric producer
  `normalChartAt.symm '' ball 0 R subset Metric.ball p s` explicit.
- The `smallNormalBall` lower-containment producer routes through the intrinsic
  radial geodesic API rather than trying to prove a metric-space containment
  directly: `normalChartAt.symm = expMap`, local
  `expMapIntrinsic = expMap`, then `smallNormalBall_radial_confined`.
- The `smallNormalBall` volume lower theorem is the honest intrinsic lower V1d
  statement before the final two-sided metric-ball theorem.  It still needs
  a density lower bound and a `g_p`-radius cap; it does not prove the Gronwall
  lower-Jacobian producer.
- The realized `Metric.ball` bridge uses `HopfRinow.riemMetric_dist_eq` and
  ENNReal `toReal`/`ofReal` conversion.  This closes the local
  `smallNormalBall` to realized-ball lower packaging, but it does not supply the
  missing density producer or the upper metric-ball-to-coordinate containment.
- The upper metric-ball-to-coordinate producer cannot honestly use one radius
  `s < R` alone: Hopf-Rinow gives a `g_p` length bound, not a Euclidean/model
  norm bound.  The checked statement uses the coercive radius condition
  `s / sqrt(gpCoerciveConst g p) < R` for the model ball, and `s < expRadiusGp`
  through the packaged `rho` to stay inside the normal-chart domain.
- The packaged upper theorem now discharges the source and coordinate
  containment hypotheses of `metricBall_vol_scale`; it still leaves
  measurability and the radial Jacobi length producer explicit.
- The density upper theorem is the matching measure-monotonicity consumer for
  the lower density shell.  It avoids routing a proved pointwise density upper
  bound back through endpoint Jacobi length data.
- The Rm04 two-sided volume wrapper is an assembly theorem, not a final
  comparison theorem: it uses the endpoint-closed Rm04 pointwise density
  wrapper, but still asks for the parallel frame family, scalar upper/lower
  model estimates, launch/Rm04 coefficient bounds, source/C2-radius controls,
  and smallness of scaled basis/unit directions.
- The Rm04 package layer is only an interface cleanup.  `Rm04FrameData` stores
  the finite index type and moving frame; `IsRm04VolHyp` records the proofs.
  It does not prove the frame, scalar model, curvature, launch, or constant
  choices.
- The scale-choice wrapper is also bookkeeping only.  It uses the checked
  `basisUnitScaleSmall` producer to choose `a` and discharge the two smallness
  fields, but the continuation still has to prove the parallel-frame,
  scalar-model, curvature, launch, and radius fields after seeing that `a`.
- The local two-sided theorem is only an assembly interface.  It packages the
  current local lower and upper estimates into one conjunction so later V1c
  producers can plug in directly, but it does not prove Gronwall, lower
  Jacobian control, or the final explicit constant theorem.
- The single-radius two-sided theorem is a bookkeeping specialization of the
  two-radius local assembly shell.  It does not add geometric content; it
  removes the lower/upper model-radius mismatch for the later capped-scale
  theorem.
- The measurable single-radius theorem removes the routine Borel measurability
  premise from the local assembly shell.  This does not prove the Gronwall
  density/Jacobi inputs or the explicit final constants.
- The new intrinsic-exponential wrappers require the usual tangent-bundle
  instance suppression used in `MinimizingGeodesic.lean`; otherwise Lean tries
  the wrong tangent-space norm/inner-product instances before the
  `RiemannianBundle`-derived ones.

Current blocker / next frontier:

- V1d's final realized metric-ball theorem is not started.  The local
  `smallNormalBall` lower theorem, realized `Metric.ball` lower packaging,
  local upper metric-ball-to-coordinate packaging, local density two-sided
  assembly, Rm04 density-to-volume wrapper, and metric-ball measurability
  discharge are now present.  The radius/scale bookkeeping wrapper is now
  present.  The next target is to prove or honestly package one non-scale
  producer feeding `IsRm04VolHyp`; the lowest-risk remaining candidates are
  launch/Rm04 coefficient bounds or scalar initial/model inequalities, while
  the parallel-frame field remains the larger geometric frontier.

Progress estimates:

- `vol_le_ball_of_len`: 100% complete.
- `vol_le_ball_of_len_radius`: 100% complete.
- `coordBall_vol_le`: 100% complete.
- `coordBall_meas`: 100% complete.
- `coordBall_vol_le_tgt`: 100% complete.
- `modelHaar_ball`: 100% complete.
- `coordBall_vol_scale`: 100% complete.
- `ball_tgt_of_radius`: 100% complete.
- `coordBall_vol_scale_c2`: 100% complete.
- `vol_ge_of_density`: 100% complete.
- `coordBall_vol_ge`: 100% complete.
- `coordBall_vol_ge_sc`: 100% complete.
- `coordBall_vol_ge_sc_c2`: 100% complete.
- `metricBall_vol_le`: 100% complete.
- `metricBall_vol_scale`: 100% complete.
- `vol_le_ball_of_density`: 100% complete.
- `metricBall_vol_scale_density`: 100% complete.
- `exists_metricBall_vol_le_dens_local`: 100% complete as a conditional local
  upper theorem from pointwise density upper bounds.
- `exists_vol_two_dens`: 100% complete as a conditional local two-sided volume
  theorem from pointwise density lower/upper bounds.
- `exists_vol_two_rm04`: 100% complete as a conditional local two-sided volume
  theorem consuming the endpoint-closed Rm04 pointwise density package; it is
  not the final V1d comparison theorem.
- `Rm04FrameData` / `IsRm04VolHyp` / `exists_vol_rm04_pkg`: 100% complete as
  a data/proof package interface for the remaining Rm04 local-volume inputs;
  they do not prove those inputs.
- `exists_rm04_scale` / `exists_vol_scale`: 100% complete as scale-choice
  packaging for the Rm04 volume theorem; they do not prove non-scale fields.
- `exists_rm04FrameData`: 100% complete as a conditional uniform
  moving-frame-data producer.  It chooses the existing single-radial-curve
  `exists_radialFrame` for each `w` in the model ball, uses `ULift (Fin n)` as
  one uniform finite index type, and returns the frame cardinality,
  parallelism, orthonormality, and `chartRepAt` differentiability fields needed
  by `Rm04FrameData`.  It assumes the per-`w` global `C^2` radial-curve
  regularity input and does not prove launch/Rm04 bounds, scalar model
  inequalities, or final constants.
- `IsRm04VolHyp.radialC2`: 100% complete as a package projection from the
  existing `hRC2` and `hb1` fields to local `C^2` regularity on `Icc 0 b` for
  every radial curve launched from the model ball.  This records the honest
  local regularity available inside the package; it does not replace the
  global smoothness still required by `exists_rm04FrameData`.
- `metricBall_vol_ge`: 100% complete.
- `metricBall_vol_ge_sc`: 100% complete.
- `metricBall_vol_ge_sc_c2`: 100% complete.
- `coordBall_subset_smallNormalBall_of_agree`: 100% complete.
- `exists_coordBall_subset_smallNormalBall`: 100% complete.
- `smallNormalBall_vol_ge_sc`: 100% complete.
- `smallNormalBall_vol_ge_sc_c2`: 100% complete.
- `exists_smallNormalBall_vol_ge_sc`: 100% complete.
- `smallNormalBall_subset_metricBall`: 100% complete.
- `metricBall_subset_smallNormalBall`: 100% complete.
- `metricBall_meas`: 100% complete.
- `exists_metricBall_vol_ge_sc_local`: 100% complete as a conditional local
  lower theorem; it is not the final V1d comparison theorem.
- `metricBall_chartCtrl`: 100% complete as a local upper containment theorem;
  it uses the correct coercivity-adjusted model radius.
- `exists_metricBall_vol_scale_local`: 100% complete as a conditional local
  upper theorem; it is not the final V1d comparison theorem.
- `exists_metricBall_vol_two_local`: 100% complete as a conditional local
  two-sided assembly theorem; it is not the final V1d comparison theorem.
- `exists_vol_two_same`: 100% complete as a conditional single-radius local
  two-sided assembly theorem; it is not the final V1d comparison theorem.
- `exists_vol_two_meas`: 100% complete as a conditional single-radius local
  two-sided assembly theorem with metric-ball measurability discharged; it is
  not the final V1d comparison theorem.
- Local `smallNormalBall` lower-volume theorem: 100% complete as a conditional
  local theorem; it is not the final metric-ball theorem.
- V1d upper/lower shell machinery: about 89% complete after the intrinsic
  Riemannian-distance lower containment, realized metric-ball lower packaging,
  coercivity-correct upper containment packaging, density-upper volume
  consumers, local density two-sided assembly, Rm04 density-to-volume wrapper,
  data/proof packaging for the remaining Rm04 inputs, automatic scale-choice
  packaging, single-radius specialization, metric-ball measurability
  discharge, conditional uniform moving-frame-data wrapper, and local
  radial-regularity package projection.
- V1d two-sided ball-volume theorem: 0% complete; no theorem with
  injectivity-radius hypotheses and explicit `s^n` scaling is stated yet.
- Stage V1: about 79% complete.
- Whole volume-comparison lane: about 54% complete; V0, V1a, endpoint V1b,
  V1c endpoint-closed density wrappers, and V1d Rm04-to-local-volume
  consumption shells plus package/scale/frame interfaces are in place, but
  explicit capped constants, actual uniform launch/Rm04/scalar producers, and
  the final two-sided theorem remain.

2026-07-08 follow-up: `exists_rm04FrameData` now connects the
`RadialGronwall.exists_radialFrame` producer to the `BallVolume.Rm04FrameData`
shape uniformly over `w in Metric.ball 0 R`.  This resolves the frame-data
packaging layer only under the explicit per-`w` radial `C^2` regularity
hypothesis.  The next concrete target is to package radial-curve regularity at
the model-ball scale, reusing `radialCurve_contMDiffOn_Icc` /
`radialCurve_contMDiffAt2` if possible and keeping the global-versus-local
regularity mismatch visible.  Launch/Rm04 coefficient bounds, scalar
upper/lower model estimates, and final capped constants remain separate
frontiers.  Verification passed for focused `BallVolume.lean` with
`-NoLakeLock` and for the targeted `Volume.BallVolume` module refresh.

2026-07-08 follow-up: `IsRm04VolHyp.radialC2` now exposes the local `C^2`
regularity that follows from the package radius fields, consuming
`RadialGronwall.radialC2OnBallIcc`.  This closes the local regularity producer
inside the V1d package, but the current frame-data producer still requires a
global `ContMDiff` curve input because `exists_parallel_frame` is global in
time.  The next concrete target is therefore not another radius wrapper; it is
either a local-on-`Icc` parallel-frame construction/API or an honest smooth
extension bridge from the local radial curve segment.  Verification passed for
focused and targeted `Volume.BallVolume`.

Verification: focused and targeted module verification passed for
`BallVolume.lean`.  No `sorry` or `axiom` occurs in this file.

2026-07-08 follow-up: added the honest smooth-extension frame layer.
`RadialExtData` records, for every `w in Metric.ball 0 R`, a globally `C^2`
curve `gamma w` equal to the original `radialCurve g p w` on `Icc 0 b`.
`exists_radialExtData` constructs this package from `0 <= b`, `b <= 1`, and
`R <= expMapC2Radius g p`, consuming `RadialGronwall.exists_radial_ext`.

`ExtFrameData` then records parallel orthonormal frame data along those
extension curves, and `exists_extFrameData` constructs it using the generic
`exists_parallel_frame`.  This is intentionally not claimed to be
`Rm04FrameData`: the remaining bridge is either to localize the volume
consumer/frame API to work on the equality interval, or to prove a dependent
transport adapter from extension-frame data back to the original radial curve
without losing endpoint differentiability/covariant-derivative hypotheses.

Verification passed for focused `BallVolume.lean` with no global Lake lock
after refreshing `Volume.RadialGronwall` once so the newly exported
`exists_radial_ext` declaration was visible.  V1d local volume shell/package
machinery remains about 89%; final V1d two-sided ball-volume theorem remains
0%.

2026-07-08 follow-up: closed the honest smooth-extension route to a radius-form
`Rm04FrameData` producer.  `RadialExtData` now records a per-launch-vector
neighborhood radius `eps` and equality on `Icc (-eps) (b + eps)`, while keeping
the old `Icc 0 b` field for existing consumers.  `radialExt_eventuallyEq`,
`radialFrameOfExt_evEq`, `rm04FrameDataOfExt_par`,
`rm04FrameDataOfExt_diff`, and `rm04FrameDataOfExt_ON` transfer the extension
frame back to the original radial curve by germ congruence.  The new
`exists_rm04FrameData_radius` produces `Rm04FrameData` directly from
`0 < b`, `b <= 1`, and `R <= expMapC2Radius g p`; it no longer assumes global
`C^2` regularity of the original radial curve.

Verification passed for focused `BallVolume.lean` with no global Lake lock.
The frame-data theorem is complete; the final V1d two-sided ball-volume theorem
is still 0%.  V1d local volume shell/package machinery is now about 91%;
Stage V1 about 80%; whole volume-comparison lane about 55%.  Next target:
connect this radius-form frame producer into the `IsRm04VolHyp` assembly path
and then attack the remaining honest producers: launch bounds, Rm04 curvature
coefficient bounds, scalar model inequalities, and final capped constants.

2026-07-08 follow-up: threaded the radius-form frame producer into the V1d
volume assembly interface.  `exists_rm04_hyp` now constructs the
`IsRm04VolHyp` proof package while automatically choosing `Rm04FrameData` via
`exists_rm04FrameData_radius`; callers still supply the non-frame producers
for launch control, Rm04 coefficient bounds, the radial-curve regularity field,
and scalar model data.  `exists_vol_frame` wraps `exists_vol_scale` so the
common scale and frame data are chosen automatically.  The proof needed the
internal frame-index universe to be fixed explicitly at `0` when calling the
existing scale/frame producers; this was a Lean elaboration issue, not a new
mathematical assumption.

Verification passed for focused `BallVolume.lean` with no global Lake lock.
This advances the package/consumer plumbing only.  The final V1d two-sided
ball-volume theorem remains 0%; V1d local volume shell/package machinery is
about 92%; Stage V1 about 80%; whole volume-comparison lane about 55%.  Next
target: pick one remaining real non-frame producer and connect it honestly,
with the global-vs-local radial-curve regularity field still visible rather
than hidden.

2026-07-08 follow-up: added the fixed-scale scalar-model bridge.
`scalarModel_smul` combines the existing `RadialGronwall` scaling lemmas
`basisModel_le_smul` and `dirModel_ge_smul`, turning unscaled fixed-basis
upper model data and unit-direction lower model data into the three scalar
fields expected by `IsRm04VolHyp` at the chosen scale.  `exists_rm04_scalar`
then constructs `IsRm04VolHyp` with radius-produced frame data and internally
scaled scalar fields, leaving launch control, Rm04 coefficient bounds, and the
radial-curve regularity input explicit.

Verification passed for focused `BallVolume.lean` with no global Lake lock.
No downstream file consumed the new declarations yet, so no targeted module
refresh was needed.  This is a scalar producer bridge, not a final comparison
theorem.  The final V1d two-sided ball-volume theorem remains 0%; V1d local
volume shell/package machinery is about 93%; Stage V1 about 80%; whole
volume-comparison lane about 56%.  Next target: either connect the scalar
bridge into a volume wrapper whose continuation chooses the scale-dependent
upper constant honestly, or close one of the remaining geometric producer
fields (`hlaunch`, `hKbound`, `hRm`, or the visible radial-curve regularity
input).

2026-07-08 follow-up: connected the fixed-scale scalar bridge to volume and
removed the explicit launch-speed producer from the latest wrapper.
`exists_vol_scalar` calls `exists_vol_rm04_pkg` directly, chooses the common
small scale, uses `exists_rm04_scalar`, and therefore exposes unscaled scalar
model data instead of the three scale-dependent scalar fields.  `exists_vol_launch`
then sets the launch bound `Vb` to the already chosen package radius `rho`,
using the existing `hρball` hypothesis to prove the required launch-speed
bound.  This avoids a new op-norm metric API and keeps the coefficient
condition honest as `sqrt(card) * Rm * rho^2 <= K`.

Verification passed for focused `BallVolume.lean` with no global Lake lock.
One attempted op-norm launch route failed at typeclass synthesis for
`||g.inner p||`; it was replaced by the simpler radius-bound route, so no
unresolved Lean error remains in the file.  The final V1d two-sided
ball-volume theorem remains 0%; V1d local volume shell/package machinery is
about 94%; Stage V1 about 81%; whole volume-comparison lane about 57%.  Next
real producers are now the Rm04 coefficient field, the visible radial-curve
regularity input, and final capped constants.

2026-07-08 follow-up: closed the algebraic Rm04 coefficient bridge.
`exists_vol_coeff` sets
`K = sqrt(card (Fin 1 -> Fin n)) * Rm * rho^2` and consumes
`exists_vol_launch`, so callers no longer provide the separate `hKbound`
field.  The scalar model inputs remain honest and are now required at this
chosen coefficient constant.  The attempted first statement used a local `let
K := ...` binder in the theorem type, which misaligned the introduced
hypotheses; the checked statement expands the coefficient expression directly.

Verification passed for focused `BallVolume.lean` with no global Lake lock.
This removes only the algebraic coefficient bound, not the actual Rm04
pointwise bound or radial-curve regularity.  The final V1d two-sided
ball-volume theorem remains 0%; V1d local volume shell/package machinery is
about 95%; Stage V1 about 81%; whole volume-comparison lane about 58%.  Next
target: replace the radial-image `hRm` input by a cleaner global or region Rm04
norm-bound producer, or confront the remaining radial-curve regularity input.

2026-07-08 follow-up: replaced the radial-image Rm04 input by reusable region
and global Rm04 norm-bound wrappers.  `exists_vol_regionRm` takes a region
`U`, a proof that every radial comparison segment lies in `U`, and a bound for
`sqrt(normSq0S metricRm04At)` on `U`; it then supplies the radial-image `hRm`
field to `exists_vol_coeff`.  `exists_vol_globalRm` is the `U = univ`
specialization.  Both wrappers keep the scalar model assumptions explicit at
the chosen coefficient constant and keep the radial-curve `C^1` input visible.

Verification passed for focused `BallVolume.lean` with no global Lake lock.
Inspection of the regularity route found that the available exponential-map
smoothness APIs prove local `ContMDiffAt` / `ContMDiffOn` on the small
comparison interval, while the current `radialJacobi_bounds` consumer still
requires global `ContMDiff` of the original radial curve.  That remaining
regularity producer is therefore not a direct local lemma; the next honest move
is a localized Gronwall/Jacobian consumer or a downstream smooth-extension
transport interface.  The final V1d two-sided ball-volume theorem remains 0%;
V1d local volume shell/package machinery is about 96%; Stage V1 about 82%;
whole volume-comparison lane about 59%.

2026-07-08 follow-up 8an: consumed the localized Rm04 density/endpoint route in
the volume package layer.  `IsRm04VolHyp.hγ` now records the local pointwise
regularity actually needed by the Gronwall consumers:
`∀ w ∈ Metric.ball 0 R, ∀ t ∈ Icc 0 b, ContMDiffAt ... (radialCurve ... w) t`.
`exists_vol_two_rm04_at` consumes `JacobianBounds.exists_dens_two_rm04_at`, and
the old `exists_vol_two_rm04` remains as a compatibility wrapper from global
`ContMDiff`.  `exists_vol_rm04_pkg` now consumes the `_at` theorem directly,
while global-regularity public wrappers convert with `hγ.contMDiffAt` when
constructing the package.

Verification passed for focused `BallVolume.lean` with no global Lake lock.
One targeted refresh of `Volume.JacobianBounds` was required first so the new
exported density `_at` declarations were visible downstream.  This closes the
local/global regularity mismatch inside the current density and volume package
stack, but it is not the final V1d two-sided ball-volume theorem: that theorem
is still 0% complete as a final capped statement.  Current honest estimates:
V1c Gronwall producer infrastructure ~99.7%; V1c determinant-bound algebraic
bridge ~93.5%; V1d local volume shell/package machinery ~97%; V1c two-sided
determinant theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1
~83%; whole volume-comparison lane ~61%.  Next target: use the already checked
`IsRm04VolHyp.radialC2` / `radialCurve_contMDiffAt_Icc` route to fill the local
`hγ` field automatically in the higher-level final-package producers, so
callers no longer supply even the local pointwise regularity manually.

2026-07-08 follow-up 8ao: filled the local radial-curve regularity package
field automatically from radius control.  `radialC1AtBall` turns
`R <= expMapC2Radius g p` and `b <= 1` into the pointwise `ContMDiffAt` field
on `Metric.ball 0 R` and `Icc 0 b`, using the already checked
`radialCurve_contMDiffAt_Icc` route.  `exists_rm04_hyp` and the later
`exists_vol_frame` package construction now set `IsRm04VolHyp.hγ` internally,
and the `exists_vol_scalar` / `exists_vol_launch` / `exists_vol_coeff` /
`exists_vol_regionRm` / `exists_vol_globalRm` chain no longer asks callers for
radial-curve regularity.  The old compatibility theorem `exists_vol_two_rm04`
still accepts global `ContMDiff` and converts it to the localized form.

Verification passed for focused `BallVolume.lean` with no global Lake lock.
No downstream module needed a targeted refresh because this pass only changed
the current file's higher-level wrappers.  This closes the hγ producer for the
current volume package stack, but it is not the final capped theorem.  Current
honest estimates: V1c Gronwall producer infrastructure ~99.8%; V1c
determinant-bound algebraic bridge ~93.5%; V1d local volume shell/package
machinery ~97.3%; V1c two-sided determinant theorem 0%; final V1d two-sided
ball-volume theorem 0%; Stage V1 ~83%; whole volume-comparison lane ~61.5%.
Next target: attack the remaining theorem-facing scalar/capped-constant inputs
for `exists_vol_globalRm` or state the next capped wrapper explicitly, while
keeping curvature boundedness as an honest input unless a compactness/continuity
producer is added.

2026-07-08 follow-up 8ap: added the time-one global Rm04 wrapper
`exists_vol_globalRm1`.  The previous `exists_vol_globalRm` interface required
`0 <= b`, `b <= 1`, and `1 <= b`, so the time parameter was already forced to
be `1`; the new wrapper fixes `b := 1` and removes that bookkeeping input from
the theorem-facing interface.  Curvature boundedness, radius/source bounds,
and the fixed scalar model inequalities remain explicit.

Verification passed for focused `BallVolume.lean` with no global Lake lock.
No targeted refresh was needed.  This is still wrapper/interface progress, not
the final capped V1d theorem.  Current honest estimates: V1c Gronwall producer
infrastructure ~99.8%; V1c determinant-bound algebraic bridge ~93.5%; V1d
local volume shell/package machinery ~97.6%; V1c two-sided determinant theorem
0%; final V1d two-sided ball-volume theorem 0%; Stage V1 ~83.3%; whole
volume-comparison lane ~62%.  Next target: either choose a capped model radius
above `exists_vol_globalRm1`, or close the remaining scalar model inequalities
from a reusable positivity/smallness lemma while keeping global Rm04 boundedness
as an explicit input.

2026-07-08 follow-up 8aq: inspected the next capped-radius/scalar route above
`exists_vol_globalRm1` and stopped before adding a misleading wrapper.  Three
routes were checked.  First, a direct radius cap would need an upper comparison
from Euclidean/model norm to `sqrt (g.inner p w w)` on the whole model ball;
the available coercivity lemma in this file goes the other direction and only
feeds `s / sqrt(gpCoerciveConst) < R`.  Second, the existing
`exists_dirModel_ge` scalar producer chooses a small time parameter `b`, but
the new global wrapper is already specialized to `b = 1`, so that route cannot
discharge the time-one lower scalar model field.  Third, the searched
Gronwall-smallness API has monotonicity/scaling lemmas and `exists_gron_small`
for choosing small `b`, but no checked time-one small-`K` or small-radius
lemma that would make the `b = 1` scalar lower model automatic.

The smallest honest next theorem is therefore a pure scalar time-one smallness
bridge: prove a reusable lemma that, from the unit-coefficient lower/upper
initial bounds, chooses or assumes a small coefficient
`K = sqrt(card) * Rm * rho^2` so
`B <= sqrt(g.inner p v v) - gronwallBound 0 (max K 1) (K * sqrt(...)) 1`
holds for every unit coefficient vector.  Until that exists, scalar model
inequalities should stay explicit in `exists_vol_globalRm1`.

2026-07-08 follow-up 8ar: consumed the time-one lower scalar model producer in
the global Rm04 volume route.  `exists_vol_rm1_ge` chooses a positive
coefficient cap `kappa` and positive endpoint constant `B`, then uses
`RadialGronwall.exists_dirModel_ge1` to fill the lower scalar model inequality
whenever
`sqrt(card (Fin 1 -> Fin n)) * Rm * rho^2 <= kappa`.  This removes
`hmodelGe` from the theorem-facing inputs of the new wrapper.

Verification passed for focused `BallVolume.lean` with no global Lake lock.
Upstream targeted refreshes of `SecondOrderGronwall` and `RadialGronwall`
passed because new exported declarations were consumed downstream.  This is
not the final capped theorem: `exists_vol_rm1_ge` still requires the upper
scalar compatibility inequality
`A + gronwallBound ... <= B` for the same produced `B`, and it still keeps
global Rm04 boundedness, source/radius bounds, and the small coefficient cap as
honest inputs.  Current honest estimates: V1c Gronwall producer infrastructure
~99.85%; V1c determinant-bound algebraic bridge ~93.5%; V1d local volume
shell/package machinery ~98%; V1c two-sided determinant theorem 0%; final V1d
two-sided ball-volume theorem 0%; Stage V1 ~83.6%; whole volume-comparison
lane ~62.5%.  Next target: prove or package the remaining upper scalar
compatibility for the same `B`, rather than adding another final-looking
wrapper that hides it.

2026-07-08 follow-up 8as: added `exists_vol_pair_rm04_at`, the local volume
wrapper that consumes `JacobianBounds.exists_dens_pair_rm04_at` and the
existing split-density integration shell `exists_vol_two_dens`.  The theorem
keeps lower and upper endpoint constants separate (`Blo` for the lower volume
bound and `Bhi` for the upper volume bound), so the higher route no longer has
to force the lower smallness-produced constant to also satisfy the upper scalar
compatibility.

Verification passed for focused `BallVolume.lean` with no global Lake lock
after the targeted refresh of `JacobianBounds`.  This is a real cleanup of the
local Rm04 volume interface, but it is not the final capped theorem: the
high-level `IsRm04VolHyp` / `exists_rm04_*` package still uses a single
constant field.  Current honest estimates: V1c Gronwall producer infrastructure
~99.85%; V1c determinant-bound algebraic bridge ~94%; V1d local volume
shell/package machinery ~98.4%; V1c two-sided determinant theorem 0%; final
V1d two-sided ball-volume theorem 0%; Stage V1 ~83.9%; whole
volume-comparison lane ~63%.  Next target: either introduce a split-constant
high-level package, or keep using the new local split wrapper directly until a
same-constant compatibility theorem is actually proved.

2026-07-08 follow-up 8at: introduced the high-level split-constant package
instead of rewriting the old same-constant package.  `IsRm04VolPairHyp` carries
the same geometric/frame/radius data as `IsRm04VolHyp`, but separates the lower
endpoint constant `Blo` from the upper endpoint constant `Bhi`.  The constructor
`exists_rm04_pair_hyp` builds this package while producing the radial frame data
and local radial-curve regularity exactly as the old constructor does.

The new packaged consumer `exists_vol_rm04_pair_pkg` consumes
`IsRm04VolPairHyp` through `exists_vol_pair_rm04_at`, proving the split lower
and upper volume bounds without touching the old compatibility API.  Focused
verification passed for `BallVolume.lean` with no global Lake lock.  No targeted
refresh was needed because no downstream file was checked against these new
exports.  Current honest estimates: V1c Gronwall producer infrastructure
~99.85%; V1c determinant-bound algebraic bridge ~94%; V1d local volume
shell/package machinery ~98.7%; V1c two-sided determinant theorem 0%; final
V1d two-sided ball-volume theorem 0%; Stage V1 ~84.1%; whole
volume-comparison lane ~63.5%.  Next target: add split versions of the
`exists_vol_scale` / `exists_vol_scalar` / `exists_vol_launch` chain so the
theorem-facing wrappers can use `Blo`/`Bhi` all the way up instead of falling
back to the same-`B` package.

2026-07-08 follow-up 8au: pushed the split-constant route through the scalar,
scale, launch, coefficient, region-Rm, and global-Rm wrapper stack.  New
wrappers `exists_vol_pair_scale`, `exists_vol_pair_scalar`,
`exists_vol_pair_launch`, `exists_vol_pair_coeff`,
`exists_vol_pair_regionRm`, and `exists_vol_pair_globalRm` mirror the old
same-constant chain but preserve `Blo` for the lower volume bound and `Bhi` for
the upper volume bound.

The time-one wrappers now avoid both scalar model inputs:
`exists_vol_pair_rm1_ge` produces the lower endpoint constant `Blo` from
`RadialGronwall.exists_dirModel_ge1`, while `exists_vol_pair_rm1_auto` chooses
the upper endpoint constant as a `max` of the upper Gronwall expression and
`0`.  Focused verification passed for `BallVolume.lean` with no global Lake
lock.  Current honest estimates: V1c Gronwall producer infrastructure
~99.9%; V1c determinant-bound algebraic bridge ~94%; V1d local volume
shell/package machinery ~99%; V1c two-sided determinant theorem 0%; final V1d
two-sided ball-volume theorem 0%; Stage V1 ~84.5%; whole volume-comparison
lane ~64%.  Remaining frontier: the theorem-facing route still requires the
small coefficient cap
`sqrt(card) * Rm * rho^2 <= kappa` and the local source/radius hypotheses.  The
next check should decide whether the cap can be made by choosing a radius after
`Rm`, or whether the current quantifier order must be changed for the final
capped theorem.

2026-07-08 follow-up 8av: added `exists_vol_two_dens_pairR`, a two-radius
metric-ball volume shell from pointwise lower and upper density bounds.  It
keeps `Rlo` for the lower model ball and `Rup` for the upper normal-coordinate
image, avoiding the same-radius pressure in `exists_vol_two_dens`.  Focused
verification passed for `BallVolume.lean` with no global Lake lock after adding
the same tensor-bundle instance workaround used by the neighboring theorem.

Remaining frontier after inspection has three failed routes:

1. Same-radius finalization is not an honest final route: it keeps both the
   lower-side condition that the model ball of radius `R` maps inside
   `Metric.ball p s` and the upper-side condition
   `s / sqrt(gpCoerciveConst) < R`.  In the Euclidean model these pull in
   opposite directions, so the final theorem should use separate `Rlo` and
   `Rup`.
2. Shrinking the theorem-facing model radius does not by itself discharge the
   coefficient cap, because the current global Rm04 chain sets `Vb := rho`;
   the cap is `sqrt(card) * Rm * rho^2 <= kappa`, not a bound involving the
   chosen smaller radius.
3. Replacing `Vb := rho` by a radius-dependent launch bound needs an upper
   comparison `sqrt(g.inner p w w) <= C * ||w||` on the model ball.  The file
   currently has only the coercive lower-direction comparison
   `||w|| <= sqrt(g.inner p w w) / sqrt(gpCoerciveConst)`, which is the wrong
   direction for this producer.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~94.2%; V1d local volume shell/package
machinery ~99.1%; V1c two-sided determinant theorem 0%; final V1d two-sided
ball-volume theorem 0%; Stage V1 ~84.8%; whole volume-comparison lane ~64.5%.
Smallest next theorem: add a local upper metric comparison/launch producer at
`p`, or change the high-level capped theorem quantifier order so the comparison
radius/launch bound can depend on `Rm`.

2026-07-08 follow-up 8aw: closed the missing local upper metric comparison API
needed by the radius-dependent launch route.  `BallVolume.lean` added the
private pointwise estimate `sqrt_inner_le_opNorm_const`, using the operator
norm of the continuous bilinear form `g.inner p`, and the private producer
`exists_metric_upper_launch_const`, which gives
`sqrt(g.inner p w w) <= C * R` on every model ball `Metric.ball 0 R`.

The split route now has public wrappers `exists_pair_rlaunch`,
`exists_pair_rcoeff`, and `exists_pair_rglobal`.  These preserve the existing
old wrappers, but add a new theorem-facing path where the curvature coefficient
cap is `sqrt(card) * Rm * (C * R)^2`, not
`sqrt(card) * Rm * rho^2`.  Focused verification passed for
`BallVolume.lean` with no global Lake lock.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~94.4%; V1d local volume shell/package
machinery ~99.25%; V1c two-sided determinant theorem 0%; final V1d two-sided
ball-volume theorem 0%; Stage V1 ~85.2%; whole volume-comparison lane ~65%.
Next target: add the radius-dependent time-one wrappers that consume
`exists_dirModel_ge1` with the cap
`sqrt(card) * Rm * (C * R)^2 <= kappa`, then choose the upper endpoint
constant by `max` as in `exists_vol_pair_rm1_auto`.  After that, the remaining
frontier is the final theorem's radius quantifier/order and the separate
lower/upper model radii from `exists_vol_two_dens_pairR`.

2026-07-08 follow-up 8ax: extended the radius-dependent route through the
time-one global Rm04 layer.  `BallVolume.lean` added `exists_pair_rglobal1`,
`exists_pair_rrm1_ge`, and `exists_pair_rrm1`.  The lower endpoint constant is
now produced from `exists_dirModel_ge1` using the cap
`sqrt(card) * Rm * (C * R)^2 <= kappa`, and the upper endpoint constant is
chosen by the same `max` pattern used in the older `rho^2` route.  Focused
verification passed for `BallVolume.lean` with no global Lake lock.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~94.6%; V1d local volume shell/package
machinery ~99.35%; V1c two-sided determinant theorem 0%; final V1d two-sided
ball-volume theorem 0%; Stage V1 ~85.6%; whole volume-comparison lane ~65.5%.
Next target: state the final small-radius theorem with quantifiers ordered so
`R` can be chosen after `Rm` and the fixed comparison constant `C`, while
keeping lower and upper model radii separate through `exists_vol_two_dens_pairR`.

2026-07-08 follow-up 8ay: inspected the final small-radius route.  Directly
wrapping `exists_pair_rrm1` is still the same-radius route and remains wrong:
it asks for both `C * R < s` on the lower side and
`s / sqrt(gpCoerciveConst) < R` on the upper side.  The honest final theorem
must still separate the lower coordinate radius from the upper normal-coordinate
radius.

Added the private scalar radius-selection helpers `exists_pos_lt_mul_sq_le` and
`exists_radius_coeff_cap`.  The latter chooses `R` after `C`, `kappa`, `rho`,
and the curvature coefficient so that `0 < R`, `R < rho`, `C * R < rho`, and
the coefficient cap holds.  Focused verification passed for `BallVolume.lean`
with no global Lake lock.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~94.7%; V1d local volume shell/package
machinery ~99.4%; V1c two-sided determinant theorem 0%; final V1d two-sided
ball-volume theorem 0%; Stage V1 ~85.8%; whole volume-comparison lane ~65.8%.
Next target: build the double-radius density/volume wrapper, using a small
lower radius for `C * Rlo < s` and a separate upper radius for
`s / sqrt(gpCoerciveConst) < Rup`; do not use `exists_pair_rrm1` as a final
single-radius theorem.

2026-07-08 follow-up 8az: added `exists_pairR_rm04_at`, the double-radius
Rm04 density-volume wrapper.  It consumes the split Rm04 pointwise density
producer on two separate model balls and feeds `exists_vol_two_dens_pairR`:
the lower bound uses `Rlo`, while the upper bound uses `Rup`.  Shared
launch/Rm/frame hypotheses are stated over the union
`Metric.ball 0 Rlo ∪ Metric.ball 0 Rup`, so the theorem no longer forces the
same radius to satisfy both lower and upper containment inequalities.  Focused
verification passed for `BallVolume.lean` with no global Lake lock.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~94.8%; V1d local volume shell/package
machinery ~99.55%; V1c two-sided determinant theorem 0%; final V1d two-sided
ball-volume theorem 0%; Stage V1 ~86.2%; whole volume-comparison lane ~66.3%.
Next target: add a double-radius proof package/automatic wrapper that supplies
the union launch/Rm/frame hypotheses from the radius-dependent global Rm04
route, then choose `Rlo` by the scalar cap helper and `Rup` from the metric-ball
upper containment constraints.

2026-07-08 follow-up 8ba: added `exists_pairR_rglobal`, the double-radius
global-Rm04 wrapper.  It keeps `Rlo` for the lower density/volume estimate and
uses `Rup` for the upper containment and shared frame package.  The proof
generates the radial frame data on `Rup`, lifts `Rlo`-ball points into the
`Rup` ball through `Rlo <= Rup`, supplies launch bounds from the fixed
`g_p`/Euclidean comparison constant `C`, and consumes a global Rm04 bound on
radial curves.  This avoids the old same-radius obstruction.

Focused verification passed for `BallVolume.lean` with no global Lake lock.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~94.95%; V1d local volume shell/package
machinery ~99.7%; V1c two-sided determinant theorem 0%; final V1d two-sided
ball-volume theorem 0%; Stage V1 ~86.7%; whole volume-comparison lane ~67%.
Next target: choose `Rlo` by `exists_radius_coeff_cap` and choose `Rup` from
the metric-ball upper containment constraints, then wrap `exists_pairR_rglobal`
into the final small-radius time-one theorem with separate lower/upper model
radii.

2026-07-08 follow-up 8bb: added `exists_pairR_rm1`, the time-one double-radius
global-Rm04 wrapper with endpoint constants generated automatically.  It
consumes `exists_pairR_rglobal`, sets `b = 1`, produces the positive lower
endpoint `Blo` through `exists_dirModel_ge1`, and chooses the upper endpoint
constant by the existing `max` pattern.  The curvature coefficient cap is
correctly placed at `Rup`, since the shared launch/frame package is built on
the upper model ball.

Focused verification passed for `BallVolume.lean` with no global Lake lock.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~95.1%; V1d local volume shell/package
machinery ~99.78%; V1c two-sided determinant theorem 0%; final V1d two-sided
ball-volume theorem 0%; Stage V1 ~87%; whole volume-comparison lane ~67.4%.
Next target: add the radius-existence theorem that, for sufficiently small
metric radius `s`, chooses `Rup` satisfying the upper containment and
coefficient cap and then chooses a smaller `Rlo` satisfying `C * Rlo < s`.

2026-07-08 follow-up 8bc: added `exists_pairR_small`, the small-radius
existence wrapper for the double-radius time-one route.  For each global Rm04
bound `Rm` and scalar initial upper bound `A`, it chooses a positive threshold
`delta`; every `0 < s < delta` admits existential model radii `Rlo` and `Rup`
with `Rlo <= Rup`, upper containment through `Rup`, and lower smallness through
`C * Rlo < s`.  The proof chooses `Rup` by `exists_radius_coeff_cap` against
`min rho expMapC2Radius`, then chooses `Rlo` by the new private helper
`exists_pos_le_mul_lt`.

Focused verification passed for `BallVolume.lean` with no global Lake lock.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~95.3%; V1d local volume shell/package
machinery ~99.9%; V1c two-sided determinant theorem 0%; final V1d two-sided
ball-volume theorem 0%; Stage V1 ~87.8%; whole volume-comparison lane ~68%.
Next target: decide the final public statement shape: either keep existential
`Rlo/Rup` as the theorem-facing API, or add explicit constants that eliminate
the existential radii from the user-facing volume comparison statement.

2026-07-08 follow-up 8bd: added `exists_pairR_scaled`, the explicit scaled
double-radius public wrapper.  It consumes the time-one double-radius theorem
and chooses fixed constants `C`, `D`, and `Blo`; for each global Rm04 bound and
scalar initial upper bound it then chooses a positive threshold `delta`, and
every `0 < s < delta` satisfies the two-sided volume estimate with explicit
model radii

- `Rlo = s / (2 * C)` on the lower side;
- `Rup = D * s` on the upper side.

The proof chooses `D = 1 + 1 / sqrt(gpCoerciveConst g p) + 1 / (2 * C)`, so
the upper containment, lower radius inclusion, and lower smallness inequalities
all follow from the same scale choice.  The remaining `s` threshold handles
`Rup <= rho`, `Rup <= expMapC2Radius`, and the coefficient cap.  This replaces
the existential-radius theorem-facing API with an explicit `s`-scaled wrapper.

Focused verification passed for `BallVolume.lean` with no global Lake lock.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~95.5%; V1d local volume shell/package
machinery ~100%; V1d explicit scaled two-sided ball-volume theorem: stated and
proved under the current global Rm04/scalar-initial hypotheses; V1c two-sided
determinant theorem 0%; Stage V1 ~89%; whole volume-comparison lane ~69.5%.
Next target: decide whether `exists_pairR_scaled` should be exported through an
umbrella/API file now, or whether the next lane should eliminate/standardize
the remaining global Rm04 and scalar initial hypotheses before treating this as
the final user-facing comparison theorem.

2026-07-08 follow-up 8be: exported the Volume comparison stack through the root
`DifferentialGeometry.lean` import list by adding `Volume.NormalChartMeasure`,
`Volume.RadialGronwall`, `Volume.JacobianBounds`, and `Volume.BallVolume`.
This makes `exists_pairR_scaled` reachable through the project umbrella without
creating a separate competing overview or wrapper file.

Focused verification passed for `DifferentialGeometry.lean` with no global Lake
lock.  `BallVolume.lean` remained focused-check green from the preceding
scaled-wrapper verification.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~95.5%; V1d local volume shell/package
machinery ~100%; V1d explicit scaled two-sided ball-volume theorem: stated,
proved, and root-exported under the current global Rm04/scalar-initial
hypotheses; V1c two-sided determinant theorem 0%; Stage V1 ~89.2%; whole
volume-comparison lane ~70%.  Next target: standardize or discharge the
remaining theorem-facing inputs (`Rm` global bound and scalar initial upper
bound `A`) if the desired final statement should no longer expose them.

2026-07-08 follow-up 8bf: added `exists_pairR_autoA`, the explicit scaled
double-radius wrapper with the scalar initial frame bound chosen automatically.
The file now has a private finite-basis norm supremum and a private
`exists_basis_upper_const` producer, which bounds the fixed `chartModelBasis`
vectors using the existing pointwise operator-norm estimate.  The public
wrapper produces `A` as one of the comparison constants instead of asking the
caller to supply the basis-bound hypothesis.

Focused verification passed for `BallVolume.lean` with no global Lake lock.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~95.7%; V1d local volume shell/package
machinery ~100%; V1d explicit scaled two-sided ball-volume theorem: stated,
proved, root-exported, and now has a verified auto-`A` public wrapper; V1c
two-sided determinant theorem 0%; Stage V1 ~89.7%; whole volume-comparison lane
~70.8%.  Next target: decide whether the remaining global Rm04 bound `Rm`
should stay as the honest theorem input for the local comparison theorem, or
whether a separate upstream geometric producer should supply it in the final
application layer.

2026-07-08 follow-up 8bg: added `Rm04GlobalBound`, a named predicate for the
remaining global pointwise Rm04 norm bound, and `exists_pairR_bound`, the
predicate-facing version of the auto-`A` scaled double-radius theorem.  This
does not prove the global curvature bound; it makes the local comparison API
honest and stable by exposing that bound under a single reusable name.

Focused verification passed for `BallVolume.lean` with no global Lake lock.

Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
determinant-bound algebraic bridge ~95.8%; V1d local volume shell/package
machinery ~100%; V1d explicit scaled two-sided ball-volume theorem: stated,
proved, root-exported, auto-`A`, and now has a named global-Rm predicate-facing
entrypoint; V1c two-sided determinant theorem 0%; Stage V1 ~90%; whole
volume-comparison lane ~71.2%.  Next target: move to the application side that
should supply `Rm04GlobalBound`, or connect this local comparison endpoint to
the broader HCG compactness input layer without weakening the theorem into a
consumer-side assumption wrapper.
