# RadialGronwall

## 2026-07-07 radial specialization of covariant Gronwall

Status: `RadialGronwall.lean` starts the V1c radial-facing producer layer.

2026-07-08 follow-up 8y: added the upper scalar/model scale bridge
`model_le_smul` and the fixed-basis field-family wrapper
`basisModel_le_smul`.  Together with `basisInit_smul_le`, this turns an
unscaled fixed-basis center-length bound and unscaled upper Gronwall model
inequality into the scaled `hinit`/`hmodelLe` shape used by
`BallVolume.IsRm04VolHyp` when the package parameter is chosen as `A = a * A0`.
This does not prove the unscaled basis bound or choose explicit final
constants; it is the algebraic transport step for those later producers.

Focused and targeted verification passed for `Volume.RadialGronwall` after
adding `model_le_smul` and `basisModel_le_smul`.

2026-07-08 follow-up 8z inspection: the parallel-frame producer is not missing
from scratch.  `exists_radialFrame` already gives a full parallel orthonormal
frame for one radial curve from `C²` radial-curve regularity and `0 < b`.
The remaining packaging frontier is to lift or thread that single-curve
producer into the `BallVolume.Rm04FrameData` shape uniformly over
`w ∈ Metric.ball 0 R`; this must still preserve the per-`w` regularity and
`chartRepAt` differentiability fields.  No new Lean declaration was added in
this inspection pass.

2026-07-08 follow-up 8w: added the common scale bookkeeping producer
`basisUnitScaleSmall`.  It combines the earlier `basisScaleSmall` and
`unitDirScaleSmall` into one positive scale `a` that makes both the fixed
model-basis vectors and every unit coefficient direction fit inside any
prescribed positive radius.  This supplies the two smallness fields needed by
`BallVolume.IsRm04VolHyp`; it does not prove the remaining parallel-frame,
scalar-model, launch, or curvature fields.

Focused and targeted verification passed for `Volume.RadialGronwall` after
adding `basisUnitScaleSmall`.

2026-07-08 follow-up 8al: added the localized radial Gronwall consumer and the
matching radial-curve pointwise regularity producer.  `radialJacobi_bounds_at`
specializes `covGronwall_bounds_at`, replacing the old global radial-curve
`ContMDiff` input by
`∀ t ∈ Icc 0 b, ContMDiffAt ... (radialCurve ...) t`; the old
`radialJacobi_bounds` remains as a compatibility wrapper.  The new
`radialCurve_contMDiffAt_Icc` packages the existing pointwise exponential-map
regularity theorem over `Icc 0 b` under `b <= 1` and
`‖x‖ < expMapC2Radius g p`.

Verification passed.  This closes the first localized Gronwall interface
brick, but it does not yet remove the top-level `hγ` field from `BallVolume`:
the `_at` interface still has to be threaded through the endpoint,
finite-direction, density, and volume wrappers.  Current honest estimates:
V1c Gronwall producer infrastructure ~99.5%; V1c determinant-bound algebraic
bridge ~93%; V1d local volume shell/package machinery ~96%; V1c two-sided
determinant theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1
~82%; whole volume-comparison lane ~59%.  Next target: add `_at` endpoint
wrappers starting at `radialJacobi_one_bounds_at`, then push them through the
finite/density layer before changing `BallVolume.IsRm04VolHyp.hγ`.

2026-07-08 follow-up 8am: completed and verified the localized endpoint and
package propagation inside `RadialGronwall.lean`.  The checked `_at` interfaces
now cover `radialJacobi_one_bounds_at`, `radialJacobi_one_le_at`,
`radialJacobi_one_ge_at`, `radialJacobi_sq_ge_at`,
`radialJacobi_dir_ge_at`, `radialJacobi_fin_le_at`,
`radialJacobi_fin_le_of_init_bound_at`,
`radialJacobi_fin_le_of_deriv_eq_at`,
`radialJacobi_fin_le_of_radius_deriv_at`,
`radialJacobi_one_le_of_scaled_radius_at`,
`radialJacobi_one_ge_of_scaled_radius_at`,
`radialJacobi_dir_ge_of_scaled_radius_at`,
`radialJacobi_fin_le_of_scaled_radius_at`, `exists_fin_le_rm04_at`, and
`exists_dir_ge_rm04_at`.  The old global-regularity theorem names remain as
compatibility wrappers that pass `fun _ _ => hγ.contMDiffAt`.

Verification passed for `RadialGronwall.lean` with focused `lake-locked check`
and no global Lake lock.  This is still infrastructure, not the V1c
two-sided determinant theorem and not the final V1d ball-volume theorem.  The
next target is to consume `exists_fin_le_rm04_at` / `exists_dir_ge_rm04_at` in
the density and `BallVolume.IsRm04VolHyp` package layer, replacing the package
field that currently asks for global `ContMDiff` by the already checked local
pointwise radial-curve regularity.  Current honest estimates: V1c Gronwall
producer infrastructure ~99.7%; V1c determinant-bound algebraic bridge ~93%;
V1d local volume shell/package machinery ~96.5%; V1c two-sided determinant
theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1 ~82%; whole
volume-comparison lane ~60%.

2026-07-08 follow-up 8r: added and verified the matching lower
unit-direction endpoint package.  `exists_dir_ge_rm04` now feeds the
endpoint-closed Rm04 data, radial `chartRepAt` differentiability, and
small-radius `D_tJ(0)=w` producer into
`radialJacobi_dir_ge_of_scaled_radius`, giving the squared lower bound for
every unit coefficient direction without asking callers to separately supply
`hJdiff`/`hDJdiff`/`hODE`/`hderivRadius`.

This completes the upper fixed-basis and lower unit-direction endpoint
producer wrappers in `RadialGronwall.lean`.  It still does not assemble the
normal-density/determinant theorem: the next handoff is to consume
`exists_fin_le_rm04` and `exists_dir_ge_rm04` in `JacobianBounds.lean`, whose
existing consumers are `normalDensity_le_of_radial_length_bound` and
`normalDensity_ge_of_dir_bound`.  That downstream edit needs a successful
`Volume.RadialGronwall` `.olean` refresh first; prior targeted refreshes of
this module have timed out, so do that only in a build window and do not start
parallel Lake jobs.  Current honest estimates: V1c Gronwall producer
infrastructure about 97%; V1c determinant-bound algebraic bridge about 91%;
V1c two-sided determinant theorem 0%; Stage V1 about 75%; whole
volume-comparison lane about 50%.

Follow-up 8s refreshed `Volume.RadialGronwall` successfully with a targeted
module build, then consumed `exists_fin_le_rm04` and `exists_dir_ge_rm04` in
`JacobianBounds.lean` as `exists_dens_le_rm04` and `exists_dens_ge_rm04`.
Focused verification passed for the downstream density wrappers.  The next
frontier is no longer the import refresh or direct consumer wiring; it is the
shared two-sided capped-density hypothesis package around these wrappers.

2026-07-08 follow-up 8q: consumed the endpoint-closed Rm04 ODE package into
the first radial analytic packages.  New checked wrappers:
`exists_rm04_data` combines `exists_radialJacobi_diff` with `exists_ode_rm04`,
returning `hJdiff`, `hDJdiff`, and `hODE` under one radius;
`exists_rm04_basis` specializes that package to the scaled fixed model-basis
directions `a • e_k`; `exists_rm04_pack` synchronizes this basis-family data
with the small-radius `D_tJ(0)=w` producer; and `exists_fin_le_rm04` feeds the
package into `radialJacobi_fin_le_of_scaled_radius`, giving the upper endpoint
fixed-basis bound without asking callers to separately supply
`hJdiff`/`hDJdiff`/`hODE`/`hderivRadius`.

This is still an upper fixed-basis endpoint package, not the final V1c
determinant theorem.  It leaves the parallel-frame assumptions, scalar model
comparison, launch-speed/Rm04 coefficient hypotheses, and the lower
unit-direction/singular-value route explicit.  The next smallest target is the
matching lower unit-direction wrapper using `exists_rm04_data` (or a shared
unit-direction package), before returning to determinant/eigenvalue assembly.
Current honest estimates: V1c Gronwall producer infrastructure about 96%;
V1c determinant-bound algebraic bridge about 91%; V1c two-sided determinant
theorem 0%; Stage V1 about 74%; whole volume-comparison lane about 49%.

Focused verification passed for `Volume.RadialGronwall` after these wrappers.
No targeted module refresh was run in this pass.

2026-07-08 follow-up 8p: the endpoint Jacobi producer is now consumed in the
Volume radial Gronwall layer.  `NormalChartMeasure.lean` exposes
`exists_radialJacobi_zero_radius`, and `RadialGronwall.lean` now has
`exists_ode_rm04`, which combines that endpoint radius with the existing
`exists_ode_rm04_jac0` / `d2_zero_of_jac0` route.  The region-wise wrapper
`exists_ode_rm04_on` also has an endpoint-closed form under the same
Riemannian-bundle and `hEnorm` hypotheses.

This closes the endpoint `IsJacobiAt ... 0` / `D_t^2 J(0)=0` producer for the
Rm04-norm and ambient-region ODE packages.  The expMap-ball and global wrappers
remain endpoint-explicit for now: pushing the endpoint-closed theorem through
those signatures exposes a tangent-ball norm compatibility boundary between
the project default tangent norm and the `RiemannianBundle` scoped norm used by
`hEnorm`.  That is a typeclass/API boundary, not a mathematical obstruction.
Current honest estimates: endpoint Jacobi producer 100%; Volume packaged
endpoint Rm04/region ODE wrapper 100%; expMap-ball/global endpoint-closed
wrappers 0%; V1c Gronwall producer infrastructure about 95%; V1c
determinant-bound algebraic bridge about 91%; V1c two-sided determinant theorem
0%; Stage V1 about 73%; whole volume-comparison lane about 48%.

Verification passed for focused `Volume.NormalChartMeasure`, targeted
`Volume.NormalChartMeasure`, and focused `Volume.RadialGronwall`.  Targeted
`Volume.RadialGronwall` was attempted only to refresh `.olean`, but timed out
after the focused check had passed and left a stale Lake lock; the stale Lake
lock was released.

2026-07-08 follow-up 6: attempted the direct model/operator-norm route for
the radial curvature term,
`||R(J, velocity) velocity|| <= ||R|| ||J|| ||velocity||^2`.  This is not the
right current layer.  Lean does not synthesize the needed `Norm` instances for
the nested tangent-space continuous-linear-map expression, and the existing
curvature-estimate infrastructure is written in terms of intrinsic
`riemannianFiberNormSq`, with nearby notes explicitly steering away from
model-space norms as theorem-facing curvature bounds.

No Lean theorem was kept from this failed route.  The smallest remaining
frontier is now to formulate the radial curvature-term estimate through the
existing intrinsic fibre-norm/orthonormal-frame API, or first add the narrow
bridge from the tangent vector term `R(J, V) V` to that API.  This is a missing
API/layer-choice issue, not a new mathematical obstruction.  Current honest
estimates remain: V1c Gronwall producer infrastructure about 74%; V1c
determinant-bound algebraic bridge about 91%; V1c two-sided determinant theorem
0%; Stage V1 about 64%; whole volume-comparison lane about 38%.

Verification after backing out the failed operator-norm attempt passed for the
focused `Volume.RadialGronwall` check.

2026-07-08 follow-up 7: completed the first intrinsic-lowering bridge for the
radial curvature term.  The reusable low-layer tensor API now has
`cotangentSharp_dualToCotangent_tangentFlat_gen` and
`cotangentInner_dualToCotangent_tangentFlat_gen` in
`Tensor/RSTensor/CotangentRiemannian.lean`.  Locally,
`RadialGronwall.lean` now defines `radialCurvTermFlat`, proves
`radialCurvTermFlat_inner`, and packages `curv_sq_of_flat_Ioo` plus
`exists_ode_Ico_of_flat`: a square-root bound for the lowered curvature
one-form on `(0, b)` feeds the existing `Ico` ODE producer.

This still does not prove the geometric curvature bound.  The next real target
is to bound `radialCurvTermFlat` using the intrinsic fibre-norm/orthonormal
frame machinery, then convert that into the flat/cotangent square-root
hypothesis.  Focused checks passed for both edited Lean files, and the targeted
`Tensor.RSTensor.CotangentRiemannian` build passed.  The targeted
`Volume.RadialGronwall` build hit a performance/tooling wall: three attempts
timed out and left stale Lake locks after the build process had exited; each
stale Lake lock was released.  Current honest estimates: V1c Gronwall producer
infrastructure about 75%; V1c determinant-bound algebraic bridge about 91%;
V1c two-sided determinant theorem 0%; Stage V1 about 64%; whole
volume-comparison lane about 38%.

2026-07-08 follow-up 8: added the next narrow bridge from the metric-lowered
radial curvature one-form to the canonical lowered Riemann tensor interface.
`RadialGronwall.lean` now has private pointwise/component bridges
`radialCurvTermFlat_apply_eq_metricRm04StdAt` and
`radialCurvTermFlat_component_eq_metricRm04StdAt`, identifying evaluation and
components of the lowered radial term with `metricRm04StdAt g q J V V W`.
It also has `radialCurvTermFlat_normSq_eq_cotangentInner` plus public
`curv_sq_of_fiber_Ioo` and `exists_ode_Ico_of_fiber`, so an intrinsic
`normSq0S` bound for the `(0,1)` lowered radial term can feed the existing ODE
producer.  This still does not prove the geometric curvature estimate from
`metricRm04At`/sectional or operator curvature bounds; it only connects the
radial term to the correct lowered-Riemann/fibre-norm API.

Follow-up 8b: added `abs_flat_apply_le_rm04`, which applies the existing
pointwise Cauchy-Schwarz theorem `abs_apply_le_sqrt_normSq0S` to bound any
evaluation of `radialCurvTermFlat` by the canonical `metricRm04At` fibre norm
times the square-root lengths of the four slots.  Focused verification passed
for `Volume.RadialGronwall` after these radial bridges.

Follow-up 8c: verified and consumed the low-layer component aggregation route.
`Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean` now has the checked
`normSq0S_le_card_of_component_bound` theorem, and
`Volume/RadialGronwall.lean` now exposes `radialCurvTermFlat_normSq_le_card`,
which turns uniform per-basis `abs_flat_apply_le_rm04` bounds into a `normSq0S`
bound for the lowered radial curvature one-form.  This is still infrastructure,
not the final geometric curvature estimate.

Current honest estimates: V1c Gronwall producer infrastructure about 77%;
V1c determinant-bound algebraic bridge about 91%; V1c two-sided determinant
theorem 0%; Stage V1 about 64%; whole volume-comparison lane about 38%.  Next
target: simplify and uniformly bound the four slot-length product from
`abs_flat_apply_le_rm04` under orthonormal basis vectors, radial-velocity
bounds, and Jacobi-field length hypotheses.

Follow-up 8d: completed that slot-length packaging layer.  The checked new
bridges are `radialCurvTermFlat_normSq_le_card_of_bounds`,
`radialCurvTermFlat_sqrt_le_card_of_velocity_bound`,
`radialCurvTermFlat_sqrt_le_K`, and `curv_sq_of_rm04_velocity_Ioo`.  Together
they reduce the radial curvature-term ODE input on `(0, b)` to pointwise
orthonormal bases, a uniform radial-velocity bound `Vb`, and a packaged
`metricRm04At` coefficient bound
`sqrt(card) * sqrt(normSq0S metricRm04At) * Vb^2 <= K`.  This still does not
produce those geometric inputs or the endpoint bound at `t = 0`; it only
packages their use by the ODE consumer.

Current honest estimates: V1c Gronwall producer infrastructure about 78%;
V1c determinant-bound algebraic bridge about 91%; V1c two-sided determinant
theorem 0%; Stage V1 about 64%; whole volume-comparison lane about 38%.  Next
target: feed `curv_sq_of_rm04_velocity_Ioo` through the existing
`exists_ode_Ico` packaging layer, then separately produce the pointwise
orthonormal bases, velocity bound, Rm04 coefficient bound, and endpoint
`t = 0` ODE input.

Follow-up 8e: added and verified `exists_ode_Ico_of_rm04_velocity`, the
radius-packaged ODE producer that consumes the pointwise orthonormal bases,
uniform radial-velocity bound, packaged Rm04 coefficient bound, and separate
endpoint `t = 0` input.  This closes the curvature-estimate packaging bridge
from lowered radial curvature through `metricRm04At` into the existing
`Ico` ODE consumer.  It still does not produce any of the four geometric
inputs.

Current honest estimates: V1c Gronwall producer infrastructure about 79%;
V1c determinant-bound algebraic bridge about 91%; V1c two-sided determinant
theorem 0%; Stage V1 about 65%; whole volume-comparison lane about 39%.  Next
target: attack the producers separately, starting with the least global one:
a radial-velocity length bound on `(0, b)` or a pointwise orthonormal-frame
supply compatible with the fixed-index theorem shape.

Follow-up 8f: added and verified the radial-speed producer and consumed it in
the Rm04 ODE package.  `radial_speed_sq_eq` exposes the Gauss-lemma constant
speed theorem in the local `radialCurve`/`curveVelocity` form, and
`radial_speed_le` turns a launch-speed bound `sqrt (g.inner p x x) <= Vb` into
the uniform radial-velocity bound on every `(0, b)` with `b <= 1`.
`exists_ode_Ico_of_rm04_launch` now shrinks the package radius by
`expMapC2Radius` and feeds this speed producer into
`exists_ode_Ico_of_rm04_velocity`.  This closes the radial-velocity producer
inside this package, but it still does not produce the pointwise orthonormal
bases, the Rm04 coefficient bound, or the endpoint `t = 0` ODE input.

Current honest estimates: V1c Gronwall producer infrastructure about 80%;
V1c determinant-bound algebraic bridge about 91%; V1c two-sided determinant
theorem 0%; Stage V1 about 65%; whole volume-comparison lane about 39%.  Next
target: build one remaining real producer separately, preferably the pointwise
orthonormal-frame supply or the Rm04 coefficient bound, while keeping the
endpoint `t = 0` ODE input as a visible separate gap.

Follow-up 8g: added and verified the pointwise ON-basis and Rm04-norm
packaging layer.  `exists_gON_tangentBasis_E` is a private witness that every
tangent fibre has a `g`-orthonormal `Module.Basis` indexed by
`Fin (finrank E)`.  `exists_ode_Ico_of_rm04` uses that witness internally, so
the public ODE package no longer asks callers to provide pointwise bases or
orthonormality proofs.  `exists_ode_Ico_of_rm04_norm` further reduces the Rm04
coefficient input to a pointwise bound
`sqrt (normSq0S metricRm04At) <= R` plus the algebraic coefficient bound
`sqrt(card) * R * Vb^2 <= K`.

The remaining gaps are now genuine producers, not packaging: (1) a radial-image
bound for `sqrt (normSq0S metricRm04At)` from the intended curvature
hypotheses, and (2) the endpoint `t = 0` ODE input.  A quick search found no
static volume-lane theorem giving the Rm04 radial-image bound; existing Rm04
norm material is mostly Ricci-flow/Shi-bound or continuity infrastructure.  On
the endpoint side, the existing radial-Jacobi initial theorem
`exists_radial_jacobi_deriv_radius` gives only `D_t J(0)=w`; no checked
`D_t^2 J(0)=0` or `IsJacobiAt`-at-`0` producer was found.

Current honest estimates: V1c Gronwall producer infrastructure about 81%;
V1c determinant-bound algebraic bridge about 91%; V1c two-sided determinant
theorem 0%; Stage V1 about 65%; whole volume-comparison lane about 39%.  Next
target: build either the radial-image Rm04 norm-bound producer from explicit
curvature hypotheses, or the endpoint `D_t^2 J(0)=0`/`IsJacobiAt`-at-`0`
producer for the radial Jacobi field.

Follow-up 8h: added and verified the endpoint-shape adapters.  The checked
`ode_Ico_of_Ioo_d2` replaces the opaque endpoint ODE inequality with the
concrete second-initial-condition input `D_t^2 J(0)=0`.  The checked
`d2_zero_of_jac0` proves that endpoint Jacobi equation at `0` implies this
second-initial-condition input, using `radialJacobi_zero` to kill the
curvature term.  The checked high-level wrappers `exists_ode_rm04_d2` and
`exists_ode_rm04_jac0` now expose the two honest remaining inputs directly:
a radial-image Rm04 norm bound and either `D_t^2 J(0)=0` or, better,
`IsJacobiAt ... 0`.

This does not prove endpoint Jacobi at `0`.  The relevant
`JacobiVariation.md` note says this endpoint needs continuity of `D^2 J` at
`0`, and no checked continuity/API producer is currently available.  The
remaining endpoint frontier is therefore a missing API lemma, not a local
algebraic rewrite.

Current honest estimates: V1c Gronwall producer infrastructure about 82%;
V1c determinant-bound algebraic bridge about 91%; V1c two-sided determinant
theorem 0%; Stage V1 about 66%; whole volume-comparison lane about 40%.  Next
target: either prove the endpoint `IsJacobiAt ... 0` via a `D^2J` continuity
producer, or build the radial-image Rm04 norm-bound producer from explicit
curvature hypotheses.

Follow-up 8i: added and verified the region-wise Rm04 packaging layer.
`rm04_Ioo_of_region` converts a `metricRm04At` fibre-norm bound on an ambient
set `U`, plus the fact that the open radial segment lies in `U`, into the
pointwise `(0, b)` curvature input consumed by the Gronwall ODE package.
`exists_ode_rm04_on` threads this through the current high-level
`exists_ode_rm04_jac0` wrapper.

This is intentionally only packaging: it does not prove the radial-image
inclusion into a normal-coordinate/curvature-control region, and it does not
prove endpoint `IsJacobiAt ... 0`.  The endpoint route remains a missing API
gap around continuity of `D^2J` at `0`; the next Rm04-side target is the
radial-image inclusion or a natural bounded-curvature-region predicate that can
feed `exists_ode_rm04_on`.  Focused verification passed.  Current honest
estimates: V1c Gronwall producer infrastructure about 83%; V1c
determinant-bound algebraic bridge about 91%; V1c two-sided determinant theorem
0%; Stage V1 about 67%; whole volume-comparison lane about 41%.

Follow-up 8j: added and verified the first concrete radial-image inclusion
producer.  `radial_mem_expBall` proves that if `‖x‖ < ρ` and `b ≤ 1`, then
the open radial segment `t ↦ exp_p(t • x)` for `t ∈ (0, b)` lies in the
`expMap` image of the open tangent ball `{v | ‖v‖ < ρ}`.  The high-level
`exists_ode_expBall` wrapper consumes an Rm04 fibre-norm bound on that
`expMap` image and feeds it through `exists_ode_rm04_on`.

This is a genuine radial-image producer, but it is still not the final
curvature estimate: callers must supply the Rm04 bound on the `expMap` image,
and the endpoint `IsJacobiAt ... 0` producer is still missing.  The next
Rm04-side target is to connect the intended curvature hypothesis to the
`expMap`-ball image bound used by `exists_ode_expBall`; the endpoint route
still needs the missing `D^2J` continuity/API bridge.  Focused verification
passed.  Current honest estimates: V1c Gronwall producer infrastructure about
85%; V1c determinant-bound algebraic bridge about 91%; V1c two-sided
determinant theorem 0%; Stage V1 about 68%; whole volume-comparison lane about
42%.

Follow-up 8k: added and verified the global-curvature-bound entry point.
`rm04Exp_of_global` restricts a global
`sqrt (normSq0S metricRm04At) <= R` hypothesis to the `expMap` ball image used
by the radial package, and `exists_ode_global` threads that through
`exists_ode_expBall`.  This matches the V1 handoff's instruction to keep the
curvature hypothesis in the same norm-bound vocabulary already consumed by the
Gronwall bricks rather than introducing a new curvature predicate.

This closes the current Rm04-side packaging route for a global `‖Rm‖ <= R`
input.  It still does not prove endpoint `IsJacobiAt ... 0`, and it does not
settle the remaining `J`/`DJ` `chartRepAt` differentiability inputs for the
Jacobi/Gronwall consumer.  Focused verification passed.  Current honest
estimates: V1c Gronwall producer infrastructure about 87%; V1c
determinant-bound algebraic bridge about 91%; V1c two-sided determinant theorem
0%; Stage V1 about 69%; whole volume-comparison lane about 43%.

Follow-up 8l: added and verified the volume-facing radial regularity wrapper.
`exists_radialJacobi_diff` exposes the checked
`Exponential/JacobiVariation.exists_jacobi_diff` theorem in the local
`radialCurve` / packaged `radialJacobiField` vocabulary, supplying both
`hJdiff` and `hDJdiff` on every capped interval `[0,b]` with `b ≤ 1`.

This closes the `J`/`DJ` `chartRepAt` differentiability producer for the
current Gronwall consumers.  The remaining V1c producer gap is now concentrated
at the endpoint: either `IsJacobiAt ... 0` or equivalently the concrete
`D_t^2 J(0)=0` input.  Focused verification passed after refreshing the missing
upstream `.olean` artifacts.  Current honest estimates: V1c Gronwall producer
infrastructure about 90%; V1c determinant-bound algebraic bridge about 91%;
V1c two-sided determinant theorem 0%; Stage V1 about 71%; whole
volume-comparison lane about 45%.

Follow-up 8m: audited the endpoint route after the clean regularity producer.
No new Lean theorem was added.  The endpoint gap is now sharpened: the missing
low-layer producer is the center acceleration of the radial exponential curve,
not another volume-facing wrapper.  The direct interior Jacobi proof cannot be
specialized to `0` because the available expMap/maximal-geodesic rescale
identity is only packaged on `[0,1]`, not as a two-sided germ at `0`; the
normal-coordinate search found first-order `mfderiv_expMap_at_zero` and
zero-section chart-flow facts but no checked acceleration API; and the
chart-flow rescale route would need a negative-scale/sign bridge before it can
feed the two-sided `covDerivAlong` definition.  Current estimates remain:
V1c Gronwall producer infrastructure about 90%; V1c determinant-bound algebraic
bridge about 91%; V1c two-sided determinant theorem 0%; Stage V1 about 71%;
whole volume-comparison lane about 45%.  Next target: prove the low-layer
radial-center acceleration producer in the exponential/gauss layer, then use it
to close `D_t^2 J(0)=0`.

Follow-up 8n: added and verified a higher-layer endpoint germ in
`Exponential/IntrinsicExp.lean`.  `exp_eq_intr_of_small` packages the existing
small chart-fixed/intrinsic exponential agreement with intrinsic foot-in-source
confinement; `exp_radial_eq_intr` proves the two-sided germ
`s |-> expMap g p (s • u) = intrinsicGeodesic g hEnorm p u s` near `0`; and
`exp_radial_geo_zero` proves the center `HasGeodesicEquationAt` for the
chart-fixed radial exponential curve under the intrinsic completeness
hypotheses.

`exp_radial_d2_zero` then combines this with the existing
`radialCurve_contMDiffAt2` C² input at `0`, proving zero covariant acceleration
for the chart-fixed radial curve at the centre.

This closes the radial-slice acceleration producer under the intrinsic
completeness hypotheses.  The remaining bridge to the V1c endpoint input is
downstream: use this slice acceleration result inside the radial Jacobi
variation endpoint proof to close the concrete `D_t^2 J(0)=0` input.  Focused
verification passed for `IntrinsicExp.lean`.  Current honest estimates: V1c
Gronwall producer infrastructure about 92%; V1c determinant-bound algebraic
bridge about 91%; V1c two-sided determinant theorem 0%; Stage V1 about 72%;
whole volume-comparison lane about 46%.  Next target: consume
`exp_radial_d2_zero` in the `JacobiVariation` endpoint argument.

Completed:

- Added `radialCurve`, the local VolumeComparison notation for the curve
  `t ↦ exp_p(t • x)` used by the radial Jacobi field.
- Added `radialJacobi_bounds`, the specialization of
  `Variation.covGronwall_bounds` to `radialJacobiField`.
- Added `radialJacobi_one_bounds`, the endpoint `t = 1` form with the same
  explicit analytic hypotheses.  This is the shape closest to
  `radialJacobiGram`.
- Added `radialCurve_one`, the endpoint bridge from `radialCurve ... 1` to the
  `expMap ... x` basepoint used by `radialJacobiGram`.
- Added `radialJacobi_one_le` and `radialJacobi_fin_le`, upper-bound
  projections of the endpoint theorem.  The latter has the exact
  `chartModelBasis` family shape consumed by the existing radial-Jacobi density
  upper-bound lemmas.
- Added `radialJacobi_fin_le_of_init_bound`, which replaces the per-basis
  scalar Gronwall expression by a uniform initial-speed bound `A` and one
  scalar model comparison.
- Added `radialCurve_zero`, `radialJacobi_init_le_of_deriv_eq`, and
  `radialJacobi_fin_le_of_deriv_eq`.  These replace the abstract initial-speed
  bound by the more geometric fixed-basis input `D_t J_k(0)=e_k` plus a
  uniform `g_p`-length bound for the fixed model basis.
- Added `fin_deriv_radius` and `radialJacobi_fin_le_of_radius_deriv`, which
  consume the small-radius derivative producer directly and expose the exact
  fixed-basis side condition `‖e_k‖ < r`.
- Added `sqrt_inner_le_of_smul_le`, `radialJacobi_one_le_of_smul`,
  `radialJacobi_one_le_of_scaled_radius`, and
  `radialJacobi_fin_le_of_scaled_radius`.  These form the scaled-basis upper
  route: apply the small-radius derivative theorem to `a • e_k`, then recover
  endpoint bounds for the original fixed basis using endpoint linearity.
- Added `basisScaleSmall`, which gives a positive common scale putting every
  fixed model-basis vector inside any prescribed positive radius, and
  `basisInit_smul_le`, which turns an original center basis-length bound into
  the scaled initial-speed bound required by the scaled route.
- Added `radialJacobi_one_ge`, `radialJacobi_sq_ge`, and
  `radialJacobi_dir_ge`.  These extract the lower half of
  `radialJacobi_one_bounds`, square it under a nonnegative model lower bound,
  and package it for every unit coefficient direction `sum_i v_i e_i`.

Route:

- This theorem discharges only the parts that are genuinely radial and already
  available: `J 0 = 0` is supplied by `radialJacobi_zero`, and the initial
  velocity in the bound is the actual covariant derivative at `0`.
- The theorem keeps the remaining producer inputs explicit: radial curve
  regularity, full parallel orthonormal frame, chart-representation
  differentiability for `J` and `D_tJ`, and the covariant second-order
  curvature ODE bound on `Ico 0 b`.
- The uniform-initial-speed bridge uses the ODE-layer
  `gronwallBound_zero_mono_eps`; it does not prove the initial-speed bound
  itself.
- The derivative-equality bridge is intentionally one step short of the
  small-radius producer: it consumes `D_t J_k(0)=e_k` for the fixed basis but
  does not prove that equality from `exists_radialJacobi_deriv_radius`.
- The radius bridge is also honest: it turns a small-radius derivative theorem
  into fixed-basis derivative equalities only under `‖chartModelBasis E k‖ < r`.
  It does not enlarge the radius and does not prove a scaling/linearity
  replacement.
- The scaled-radius bridge avoids raw-basis smallness for the upper endpoint
  bound, but only at the endpoint.  It still requires analytic hypotheses for
  the scaled Jacobi fields, smallness of `a • chartModelBasis E k`, and a
  scaled model comparison `... <= a * B`.
- The common-scale helper discharges the existence of a positive `a` for
  scaled-basis smallness.  It does not choose analytic hypotheses or prove the
  scalar model inequality; those remain theorem-facing inputs.
- The lower endpoint producer is still conditional.  It turns an explicit
  lower scalar Gronwall comparison into the inner-product lower bound required
  by the density route, but it does not build the regularity, parallel-frame,
  ODE/curvature, or initial-speed lower package.
- `exists_unitCoeff_ge` is the first lower-route initial-length producer for
  unit coefficient directions.  It uses the `toEuclidean.symm` realization of
  the fixed chart model basis, `ContinuousLinearEquiv.antilipschitz`, and
  `gpCoerciveConst_le` to get a uniform positive lower bound for
  `sqrt (g_p (sum_i v_i e_i) (sum_i v_i e_i))` when `||v|| = 1`.  It does not
  prove the Jacobi initial-derivative equality
  `D_t J_{sum_i v_i e_i}(0) = sum_i v_i e_i`.
- `exists_unitCoeff_le` supplies the matching finite-dimensional uniform upper
  bound for the same coefficient directions, using `coeffModelCLM` and the
  operator norm of `g.inner p`.  `exists_unitCoeff_bounds` packages the lower
  and upper constants as the natural scalar data for the lower model route.
- `dir_deriv_radius`, `dir_init_ge`, and `exists_dirInit_ge` now connect the
  lower-route coefficient bound to the Jacobi initial-speed expression once the
  initial derivative equality is available.  The radius bridge deliberately
  keeps the side condition `||sum_i v_i e_i|| < r` explicit for unit
  coefficient vectors; discharging that side condition, or replacing it with a
  scaling/linearity route, remains the next real frontier.

Current blocker / next frontier:

- The final V1c radial-Jacobi determinant theorem is still not started.  The
  upper endpoint route now has the scale-existence and scaled-initial-speed
  algebra.  The next missing API is the analytic package for the scaled basis
  fields: radial regularity, parallel orthonormal frame, `chartRepAt`
  differentiability for `J_{a e_k}` and `D_tJ_{a e_k}`, the curvature/ODE
  bound, and the scaled scalar model comparison.  The lower route now has the
  unit-direction endpoint lower consumer/producer shape and the coefficient
  `g_p` initial-length lower bound, a conditional initial-speed package, a
  common-scale smallness producer, and the scaled-radius lower endpoint bridge.
  `dirModel_ge_of_bounds` reduces the unscaled lower scalar model comparison to
  the packaged constants `B0`, `D`, and one scalar smallness inequality, and
  `exists_dirModel_ge` now supplies positive `b,B` satisfying that inequality.
  The remaining lower-route frontier is the scaled analytic package and Jacobi
  initial-derivative bridge; `dirModel_ge_smul` then transports the unscaled
  model comparison to the scaled route.

Progress estimates:

- `radialJacobi_bounds`: 100% complete as a conditional radial specialization
  theorem; it is not the regularity or curvature-bound producer.
- `radialJacobi_one_bounds`: 100% complete as a conditional endpoint
  specialization theorem; it is not the endpoint-length producer by itself.
- `radialJacobi_one_le` / `radialJacobi_fin_le`: 100% complete as conditional
  endpoint-length producers; they still require the analytic hypotheses and the
  scalar model-bound input.
- `radialJacobi_fin_le_of_init_bound`: 100% complete as a conditional
  uniform-initial-speed endpoint producer; it still requires `hinit`.
- `radialJacobi_fin_le_of_deriv_eq`: 100% complete as a conditional endpoint
  producer from fixed-basis derivative equalities; it still requires those
  equalities and the analytic hypotheses.
- `radialJacobi_fin_le_of_radius_deriv`: 100% complete as a conditional
  endpoint producer from a small-radius derivative theorem; it still requires
  fixed-basis smallness.
- `radialJacobi_fin_le_of_scaled_radius`: 100% complete as a conditional upper
  endpoint producer from scaled-basis smallness; it is not the analytic package
  or lower determinant producer.
- `basisScaleSmall`: 100% complete as the common positive scale existence
  lemma; it is not the analytic package.
- `basisInit_smul_le`: 100% complete as the scaled initial-speed algebra from
  an original center basis-length bound.
- `model_le_smul` / `basisModel_le_smul`: 100% complete as the upper
  scalar/model scaling bridge for the fixed-basis `hinit`/`hmodelLe` package
  fields; they do not prove the unscaled basis bound or final constants.
- `radialJacobi_one_ge` / `radialJacobi_sq_ge` / `radialJacobi_dir_ge`: 100%
  complete as conditional lower endpoint producers; they are not the analytic
  package or lower scalar model comparison.
- `exists_unitCoeff_ge`: 100% complete as a coefficient-space `g_p`
  initial-length lower producer; it is not the Jacobi initial-derivative
  equality or scalar Gronwall-error package.
- `exists_unitCoeff_le` / `exists_unitCoeff_bounds`: 100% complete as the
  matching coefficient-space upper producer and two-sided initial-length
  package for unit coefficient directions; they are not the analytic Jacobi
  package.
- `dir_deriv_radius`: 100% complete as a conditional unit-coefficient
  derivative bridge from the radius theorem; it still requires unit-direction
  smallness.
- `dir_init_ge` / `exists_dirInit_ge`: 100% complete as conditional
  initial-speed lower packages from a supplied Jacobi initial-derivative
  equality; they are not the analytic package or the scalar model-error
  comparison.
- `unitDirScaleSmall`: 100% complete as a common-scale smallness producer for
  all unit coefficient directions.
- `radialJacobi_one_ge_of_smul` /
  `radialJacobi_one_ge_of_scaled_radius`: 100% complete as the single-direction
  lower scaled-radius endpoint bridge.
- `radialJacobi_dir_ge_of_scaled_radius`: 100% complete as the unit-direction
  lower scaled-radius endpoint bridge; it still requires the scaled analytic
  hypotheses and a scalar lower model comparison.
- `model_ge_of_smul` / `dirModel_ge_smul`: 100% complete as scalar/metric
  scaling adapters for lower Gronwall model comparisons; they are not the
  unscaled lower model comparison itself.
- `dirModel_ge_of_bounds`: 100% complete as a monotonicity adapter reducing the
  unit-direction lower scalar model comparison to uniform initial lower/upper
  bounds and one scalar smallness inequality; it is not the analytic package.
- `exists_dirModel_ge`: 100% complete as the lower-route scalar existence
  package producing positive `b,B` for all unit coefficient directions; it is
  not the radial analytic package or Jacobi initial-derivative bridge.
- V1c Gronwall producer infrastructure: about 99% complete after the fixed-space
  Gronwall wrappers, covariant transfer theorem, radial specialization,
  endpoint wrapper, endpoint bridge, basis-family upper-bound producer, and
  uniform-initial-speed/derivative-equality/radius/scaled-radius/common-scale
  scalar compression, plus the conditional lower unit-direction endpoint
  producer, coefficient-space initial-length lower and upper bridges,
  two-sided coefficient package, conditional unit-direction initial-speed
  package, common-scale unit-direction smallness, lower scaled-radius endpoint
  bridge, upper/lower scalar model scaling adapters, scalar lower-model
  monotonicity adapter, positive scalar lower-model existence package, and the
  fixed-basis upper scalar/model scale bridge.  The missing pieces are now
  mostly the geometric/analytic producers consumed by the Rm04 package, not the
  scalar algebra in this file.
- V1c two-sided determinant theorem: 0% complete; no capped-scale determinant
  theorem is stated yet.
- Stage V1: about 78% complete.
- Whole volume-comparison lane: about 53% complete.

Verification: focused verification and targeted module verification passed for
`RadialGronwall.lean` after adding the scaled-radius bridge and again after
adding `basisScaleSmall` / `basisInit_smul_le`; downstream targeted
verification also passed through `JacobianBounds.lean` and `BallVolume`.
Focused verification and targeted module verification passed again after adding
the lower endpoint producer lemmas; downstream targeted verification again
passed through `JacobianBounds.lean` and `BallVolume`.
Focused verification and targeted module verification passed after adding
`exists_unitCoeff_ge`; downstream targeted verification also passed through
`JacobianBounds.lean` and `BallVolume`.
Focused verification and targeted module verification passed after adding
`exists_unitCoeff_le`, `exists_unitCoeff_bounds`, and `dirModel_ge_of_bounds`;
downstream targeted verification again passed through `JacobianBounds.lean` and
`BallVolume`.
Focused verification and targeted module verification passed after adding
`exists_dirModel_ge`; downstream targeted verification again passed through
`JacobianBounds.lean` and `BallVolume`.
Focused verification passed after adding `dir_deriv_radius`, `dir_init_ge`, and
`exists_dirInit_ge`; targeted module verification and downstream targeted
verification also passed through `JacobianBounds.lean` and `BallVolume`.
Focused verification passed after adding `unitDirScaleSmall`,
`radialJacobi_one_ge_of_smul`, `radialJacobi_one_ge_of_scaled_radius`,
`radialJacobi_dir_ge_of_scaled_radius`, `model_ge_of_smul`, and
`dirModel_ge_smul`; targeted module verification and downstream targeted
verification also passed through `JacobianBounds.lean` and `BallVolume`.

2026-07-08 update: `exists_radialFrame` is 100% complete as the
radial-facing full parallel orthonormal frame producer from `C²` radial curve
regularity and a positive interval endpoint.  It reuses the existing
orthonormal-basis existence theorem and `exists_parallel_frame`; it does not
prove radial curve regularity, Jacobi-field differentiability, the Jacobi ODE
bound, or the initial-derivative bridge.

The live V1c analytic-package frontier is now smaller: the parallel-frame
sub-block is packaged, but the remaining producer must still supply radial
curve regularity at the chosen scaled radius, `chartRepAt` differentiability
for `J` and `DJ`, the ODE/curvature hypotheses consumed by
`radialJacobi_*`, and the Jacobi initial-derivative bridge.  Current honest
estimates: V1c Gronwall producer infrastructure about 69%; V1c
determinant-bound algebraic bridge about 91%; V1c two-sided determinant
theorem 0%; Stage V1 about 62%; whole volume-comparison lane about 37%.

Verification passed for focused and targeted `Volume.RadialGronwall`, plus
downstream targeted builds through `Volume.JacobianBounds` and
`Volume.BallVolume`.

2026-07-08 follow-up 8ar: added the time-one lower scalar model producer
`exists_dirModel_ge1`.  It consumes the existing unit-coefficient lower/upper
initial bounds and the new scalar lemma `exists_gron_smallK`, choosing a small
coefficient cap `K` and a positive endpoint lower constant `B`.  For every
`0 <= k <= K`, it proves the lower scalar model inequality at endpoint time
`1` for all unit coefficient vectors.

Verification passed for focused `Volume.RadialGronwall`; a targeted refresh of
`Volume.RadialGronwall` passed before `BallVolume` consumed the new exported
declaration.  This closes the lower scalar model field at fixed time when the
curvature coefficient is small, but it does not choose an upper scalar model
constant compatible with the same `B`.  Current honest estimates: V1c Gronwall
producer infrastructure ~99.85%; V1c determinant-bound algebraic bridge
~93.5%; V1c two-sided determinant theorem 0%; Stage V1 ~83.5%; whole
volume-comparison lane ~62.5%.  Next target: either prove upper/lower scalar
constant compatibility at small coefficient, or keep the upper scalar
inequality explicit in the volume theorem-facing wrapper.

2026-07-08 follow-up 4: added the endpoint-safe smooth-extension producers
`exists_rclip_nbhd` and `exists_rext_nbhd`.  They choose a smooth bounded time
clip that is the identity on a window `Icc (-eps) (b + eps)` around `Icc 0 b`
while keeping every clipped launch vector inside `expMapC2Radius g p`, then
package the corresponding globally `C^2` radial extension.  This supersedes
the closed-interval-only extension for frame transport: endpoint
differentiability and `covDerivAlong` transfer need neighborhood equality, not
just equality on `Icc 0 b`.

Verification passed for focused `Volume.RadialGronwall` with no global Lake
lock, plus one targeted module refresh because `BallVolume` consumed the new
exports.  V1c determinant theorem remains 0%; this work belongs to V1d frame
producer infrastructure.

2026-07-08 follow-up 8ac: added `exists_radial_clip`, consuming the
`Variation.PerpFrame.exists_time_clip` smooth time reparametrization in the
radial setting.  Given `0 <= b`, `b <= 1`, and
`‖x‖ < expMapC2Radius g p`, it produces a globally smooth `tau : ℝ -> ℝ`
equal to the identity on `Icc 0 b` and satisfying
`‖tau t • x‖ < expMapC2Radius g p` for every `t`.  This is the honest
smooth-extension bridge below the frame API: it still does not itself produce
a global `ContMDiff` radial curve or a localized parallel-frame construction.

Focused verification passed for `Volume.RadialGronwall` with no global Lake
lock.  No targeted module refresh was run because no downstream file consumed
the new declaration yet.  Current honest estimates: V1c Gronwall producer
infrastructure about 99%; V1c determinant-bound algebraic bridge about 93%;
V1d local volume shell/package machinery about 89%; V1c two-sided determinant
theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1 about 79%;
whole volume-comparison lane about 54%.  Next target: compose the clipped
time parameter with the radial exponential curve to prove a global smooth
radial extension, or localize the frame API directly to `Icc 0 b`.

2026-07-08 follow-up 8ad: completed the clipped radial global-smoothness
bridge.  `radial_clip_contMDiff` proves that any smooth time clip whose
launch vectors stay inside `expMapC2Radius g p` gives a globally `C^2`
clipped radial exponential curve.  `exists_radial_ext` packages this with
`exists_radial_clip`, producing a globally `C^2` curve equal to the original
`radialCurve g p x` on `Icc 0 b`.

Focused verification passed for `Volume.RadialGronwall` with no global Lake
lock.  This still does not produce `Rm04FrameData`: the remaining frame-data
frontier is to transfer a parallel frame constructed along the smooth
extension back to the original radial curve on the equality interval, or to
localize the frame API so no dependent fiber transport is needed.  Current
honest estimates remain: V1c Gronwall producer infrastructure about 99%;
V1c determinant-bound algebraic bridge about 93%; V1d local volume
shell/package machinery about 89%; V1c two-sided determinant theorem 0%;
final V1d two-sided ball-volume theorem 0%; Stage V1 about 79%; whole
volume-comparison lane about 54%.

2026-07-08 follow-up 8aa consumption note: `exists_radialFrame` is now consumed
by `BallVolume.exists_rm04FrameData`, which packages the single-curve parallel
orthonormal frame producer uniformly over `w in Metric.ball 0 R` using the
`BallVolume.Rm04FrameData` record.  This did not require changing
`RadialGronwall.lean`.  The remaining regularity frontier is still to supply
the per-`w` radial `C^2` hypothesis in the shape required by that wrapper,
preferably from the existing `radialCurve_contMDiffOn_Icc` /
`radialCurve_contMDiffAt2` route if the local/global statement mismatch can be
bridged honestly.

2026-07-08 follow-up 8ab: `radialC2OnBallIcc` is 100% complete as the honest
model-ball local-regularity producer.  It turns `R <= expMapC2Radius g p` and
`b <= 1` into `ContMDiffOn` `C^2` regularity for every radial curve launched
from `w in Metric.ball 0 R` on `Icc 0 b`, by reusing
`radialCurve_contMDiffOn_Icc`.  This deliberately does not produce the global
`ContMDiff` hypothesis still required by the current `exists_parallel_frame`
API; that remains a local/global frame-construction frontier, not a scalar or
radius-bookkeeping problem.  Verification passed for focused and targeted
`Volume.RadialGronwall`.

2026-07-08 follow-up 8o: the endpoint Jacobi equation producer is now checked in
`Exponential/JacobiVariation.lean`.  `exists_jacobi_zero` gives the radius
packaged `IsJacobiAt ... 0` statement for the clean radial variation under the
intrinsic completeness / continuous Riemannian-bundle hypotheses and explicit
`hEnorm`.  It uses the newly checked `clamped_slice_covDeriv_velocity_zero_at_zero`,
which transfers the clamped radial slice at `0` to
`Exponential.exp_radial_d2_zero`.

This closes the mathematical endpoint-Jacobi producer in the exponential layer.
The remaining Volume-layer bridge is packaging, not the endpoint proof itself:
combine `exists_jacobi_zero` with the local `radialJacobiField` vocabulary and
`d2_zero_of_jac0`.  Two direct wrappers were tried and reverted because the
public theorem heads in `RadialGronwall` / `NormalChartMeasure` exposed
`IsContinuousRiemannianBundle` / `FiberBundle` / `VectorBundle` instance
plumbing.  The next smallest target is therefore an adapter in a context that
already carries the full tangent-bundle instance chain, or a small local section
that installs those instances before stating the wrapper.  Focused verification
passed for the touched Lean files after reverting the failed adapters.

Current honest estimates: endpoint Jacobi theorem `exists_jacobi_zero` 100%;
Volume packaged endpoint `D_t^2 J(0)=0` wrapper 0%; V1c Gronwall producer
infrastructure about 94%; V1c determinant-bound algebraic bridge about 91%;
V1c two-sided determinant theorem 0%; Stage V1 about 72%; whole
volume-comparison lane about 47%.

2026-07-08 follow-up 5: `curv_sq_of_norm_Ioo` and
`exists_ode_Ico_of_curvNorm` are 100% complete as the curvature-bound packaging
layer.  The new private `radialCurvTerm` only abbreviates the existing
`riemannOp(J, velocity, velocity)` term.  The public wrapper converts a
square-root curvature-term estimate on `(0, b)` into the squared `hODE`
curvature input used by `exists_ode_Ico`, assuming `0 <= K`.

This still does not prove the geometric curvature estimate itself; it only
normalizes the shape future geometry producers should target.  The final V1c
two-sided determinant theorem is still not stated and remains 0% complete.
The remaining frontier is now: (1) prove the actual radial curvature-term
norm estimate on `(0, b)`, (2) prove or package the endpoint ODE bound at
`t = 0`, and (3) prove or package the `J`/`DJ` `chartRepAt`
differentiability inputs.  The endpoint route still looks like a missing
two-sided rescale/geodesic API unless a different proof is found.  Next
target: attack the actual curvature-term norm estimate, using existing
curvature operator/fibre-norm infrastructure where possible.  Current honest
estimates: V1c Gronwall producer infrastructure about 74%; V1c
determinant-bound algebraic bridge about 91%; V1c two-sided determinant
theorem 0%; Stage V1 about 64%; whole volume-comparison lane about 38%.

Verification passed for focused and targeted `Volume.RadialGronwall`, plus
downstream targeted builds through `Volume.JacobianBounds` and
`Volume.BallVolume`.

2026-07-08 follow-up 4: `exists_ode_Ico` is 100% complete as the
radius-packaged ODE-input producer.  It consumes `exists_jacobi_Ioo` and
`ode_Ico_of_Ioo_zero`, so future callers no longer need to pass an explicit
open-interval Jacobi predicate; they still provide the open-interval
curvature-term bound and the separate endpoint ODE bound at `t = 0`.

This is still infrastructure, not the final V1c two-sided determinant theorem.
The theorem itself is not stated and remains 0% complete.  The remaining
frontier is to prove or package the endpoint ODE bound at `t = 0`, the
curvature-term norm estimate on `(0, b)`, and the `J`/`DJ` `chartRepAt`
differentiability inputs.  The direct endpoint route inspected so far needs a
two-sided local rescale/geodesic identity near `0`; the public rescale wrapper
currently exposes only the `[0, 1]` interval, so that route is a missing API
gap unless another endpoint proof is found.  Next target: package the
curvature-term bound on `(0, b)` while keeping the endpoint gap visible.
Current honest estimates: V1c Gronwall producer infrastructure about 73%;
V1c determinant-bound algebraic bridge about 91%; V1c two-sided determinant
theorem 0%; Stage V1 about 63%; whole volume-comparison lane about 37%.

Verification passed for focused and targeted `Volume.RadialGronwall`, plus
downstream targeted builds through `Volume.JacobianBounds` and
`Volume.BallVolume`.

2026-07-08 follow-up 3: `exists_jacobi_Ioo` and
`ode_Ico_of_Ioo_zero` are 100% complete as the interior radial-Jacobi ODE
packaging layer.  `exists_jacobi_Ioo` turns the existing radius theorem for
`(0, 1)` into a radius theorem on every smaller `(0, b)` with `b <= 1`.
`ode_Ico_of_Ioo_zero` then assembles the Gronwall `Ico 0 b` ODE input from
open-interval Jacobi/curvature data plus one separate endpoint bound at
`t = 0`.

This deliberately does not prove the endpoint bound, the curvature-term norm
bound, or the `J`/`DJ` `chartRepAt` differentiability inputs.  The live
frontier is now narrower: produce the endpoint ODE bound at `t = 0`, package
the curvature-term bound on `(0, b)`, and prove or package the `J`/`DJ`
differentiability hypotheses.  Current honest estimates: V1c Gronwall
producer infrastructure about 72%; V1c determinant-bound algebraic bridge
about 91%; V1c two-sided determinant theorem 0%; Stage V1 about 63%; whole
volume-comparison lane about 37%.

Verification passed for focused and targeted `Volume.RadialGronwall`, plus
downstream targeted builds through `Volume.JacobianBounds` and
`Volume.BallVolume`.

2026-07-08 follow-up 2: `radialJacobi_ode_of_curv` is 100% complete as the
radial-facing ODE adapter from pointwise `IsJacobiAt` plus a curvature-term
norm bound to the exact `hODE` shape consumed by `radialJacobi_*`.  It uses the
new generic `Variation.ode_bound_of_isJacobiAt`; it does not prove the
curvature-term bound, the `t = 0` Jacobi endpoint, or the `J`/`DJ`
`chartRepAt` differentiability hypotheses.

The live analytic-package frontier is now split cleanly: (1) get pointwise
Jacobi data on the needed `Ico` interval, including the endpoint shape not
covered by the existing `exists_radialJacobi_radius` `Ioo` theorem; (2) prove
or package the curvature-term bound; (3) prove or package `chartRepAt`
differentiability for `J` and `DJ`.  Current honest estimates: V1c Gronwall
producer infrastructure about 71%; V1c determinant-bound algebraic bridge
about 91%; V1c two-sided determinant theorem 0%; Stage V1 about 63%; whole
volume-comparison lane about 37%.

Verification passed for focused and targeted `Variation.JacobiField` and
`Volume.RadialGronwall`, plus downstream targeted builds through
`Volume.JacobianBounds` and `Volume.BallVolume`.

2026-07-08 follow-up: `radialCurve_contMDiffOn_Icc` is 100% complete as the
interval `C²` regularity wrapper for the radial curve under
`‖x‖ < expMapC2Radius g p`.  It reuses the existing pointwise
`radialCurve_contMDiffAt2` theorem and proves the smallness of `t • x` on
`[0, 1]`.  This closes the honest interval-regularity sub-block, but it does
not provide the global `ContMDiff` hypothesis required by the current
`exists_parallel_frame` wrapper; that mismatch should stay visible until the
frame API is localized or an honest smooth extension is introduced.

The next analytic-package target is now the Jacobi side: produce or package
the `chartRepAt` differentiability for the radial Jacobi fields and their
covariant derivatives, plus the ODE/curvature hypotheses consumed by
`radialJacobi_*`.  Current honest estimates: V1c Gronwall producer
infrastructure about 70%; V1c determinant-bound algebraic bridge about 91%;
V1c two-sided determinant theorem 0%; Stage V1 about 62%; whole
volume-comparison lane about 37%.

Verification passed for focused and targeted `Volume.RadialGronwall`, plus
downstream targeted builds through `Volume.JacobianBounds` and
`Volume.BallVolume`.
