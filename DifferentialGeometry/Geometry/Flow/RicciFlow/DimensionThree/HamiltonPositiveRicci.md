# HamiltonPositiveRicci live frontier audit

## Fixed-time improved-pinching producers — 2026-07-24

The source and scale sides of the fixed-time Hamilton pinching argument now
have checked producers.

- `ham3_tf_display` proves the exact parabolic scaling law for
  `tfRicNormSq`.
- `ham3_tf_bound0` combines that scaling law, scalar positivity on the
  original carrier, the selected-rescaling scalar bound, and
  `Ham3PinchEstimate` to obtain the uniform estimate
  `q_i(0,x) ≤ C * Q_i ^ (-epsilon)`.
- `ham3_scale_atTop` derives `Q_i → ∞` from finite maximal time and
  `Q_i * t_i → ∞`.
- `ham3_scale_decay` restricts to the smooth-CGH subsequence and proves
  `C * Q_i ^ (-epsilon) → 0`.

Focused and exact source verification pass.  These source-bound and
scale-decay producers and their dedicated algebraic machinery are **100%**.

The actual fixed-time theorem
`HamiltonPositiveRicciAdapter.tf_decay0_of_cgh : LimitTfDecayAt L 0` is now
focused-green, so both that theorem and its dedicated machinery are **100%**.
Cross-model naturality, C2-jet convergence of the intrinsic squared Ricci norm,
and closed/open `ConvOut` retention through `FlowLimitData` are checked; the
fully evaluated scalar combination
`|Ric|² - scalar² / 3` then passes to the limit without a tensor-valued
transport.  A scalar strong maximum principle and the older all-time
`Ham3PinchTransfer` package are not needed for this time-zero route.  The
adapter's exact artifact refresh is still running at this snapshot.

Consequently `ham3_cgh_limit` remains theorem-level **0%**, while whole-project
HCG infrastructure remains conservatively about **60%**.

## Time-zero roundness reducers — 2026-07-24

Two fixed-slice consumers now isolate the book-faithful time-zero route from
the stronger all-window scalar-positivity package.

- `tf_zero_of_decay` proves `LimitTfZeroAt L t` directly from
  `LimitTfDecayAt L t` and the three-dimensional model-space hypothesis.  The
  older `limit_tf_zero_of_decay` theorem remains as the all-regular-times
  compatibility wrapper.
- `limit_round_base` proves `LimitRoundAt L t` from the Einstein equation,
  connectedness, boundarylessness, and positivity of scalar curvature only at
  the CGH base point.  Schur constancy supplies positivity everywhere.  The
  older `limit_round_of_ein` theorem remains as the compatibility wrapper for
  callers carrying `LimitScalarPosAt`.

The focused source verification passes.  Both new theorems and their dedicated
consumer machinery are **100%**.  They add no analytic assumption and show that
the static Hamilton endgame does not require a strong maximum principle.

The missing endpoint-time CGH transfer is now proved by
`HamiltonPositiveRicciAdapter.tf_decay0_of_cgh`.  Composing it with these
reducers and the already retained base-scalar convergence is the next narrow
assembly step.  `ham3_cgh_limit` itself remains theorem-level **0%**, and
whole-project HCG infrastructure remains conservatively about **60%**.

## `ham3_space_box` endpoint integration — 2026-07-24

The natural universal-cover construction exposed a declaration-level universe
bug in `SphericalSpaceFormQuotientModel`: its quotient and deck-group universes
were both pinned to `Type 0`, while a manifold `M : Type u`, its standard-model
copy, and `FundamentalGroup M default` all naturally remain in `Type u`.  The
model now stores
`RoundQuotientData.{0, u, u} (EuclideanSpace Real (Fin 4)) 3`.
Its carrier argument is also explicitly `N : Type u`, so the otherwise hidden
quotient universe is determined by the supplied manifold rather than remaining
an unification metavariable in `IsSphericalSpaceFormQuotient`.
This changes no mathematical assumptions and avoids an artificial finite-group
reindexing layer.

`ham3_space_box` now has a complete proof.  It consumes the geometry-native
`constPosQuotient` data producer, which:

- re-presents the manifold over `𝓡 3` using `stdModelCopy`;
- pulls the constant-curvature metric across the standard-model
  diffeomorphism;
- normalizes and lifts the metric to the universal cover;
- applies the positive Killing--Hopf theorem in the correct intrinsic
  pseudo-metric/uniformity world;
- conjugates the deck action to orthogonal sphere isometries and returns
  `RoundQuotientData` whose carrier is definitionally the standard-model copy.

The first axiom audit found that this path inherited the former
`fibre_countable` `sorry` through the universal-cover
`instSigmaCompactSpace`.  The polygonal-loop code now records a
path-connected basis refinement at every internal subdivision vertex, so it
does not assume that arbitrary pairwise basis intersections are path
connected.

The final `CountablePi1 -> Manifold -> PositiveSpaceForm -> Hamilton` exact
replay passes.  The axiom audit for `ham3_space_box`, `constPosQuotient`, the
Killing--Hopf and deck-quotient producers, `fibre_countable`, and
`instSigmaCompactSpace` reports only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.

Accordingly, the `ham3_space_box` theorem and its dedicated machinery are both
trusted and **100%**.  The only remaining theorem-body `sorry`s in the
Hamilton file are the separate `ham3_flow_exists_normalized` and
`ham3_cgh_limit` producers; each remains theorem-level 0%.  Whole-project HCG
infrastructure remains conservatively about **60%**.

## Current state — 2026-07-23

`ham3_noncollapse` is now proved.  It installs the compact, connected, and
boundaryless instances carried by `Closed3Manifold`, obtains the actual
`IsSolutionOn P.S`, applies the axiom-clean Perelman producer
`no_local_open`, and feeds that result to the already checked
`ham3_noncollapse_of` adapter.  Its focused source check passes.  Thus
`ham3_noncollapse` is theorem-level **100%**, and its dedicated noncollapsing
machinery is **100%**; this is no longer one of the Hamilton `sorry`
frontiers.

The exact Hamilton target rebuilt the full Noncollapsing chain successfully
(`ConjGalerkinClassical`, `ConjGalerkinOn`, `WSpan`, `NoncollapseSpan`,
`NoncollapseOpen`, and `EarlyBall`) but stopped at **10128/10129** on the
unrelated shared module `Evolution/BBSLimitProducer.lean`: lines 104 and 142
try to eliminate an `Exists` proof into `CinftyLimitData`, which Lean rejects
because `Exists.casesOn` can eliminate only into `Prop`.  `MovingShiOpen` did
not fail and was not edited by this lane.

That failure was imported only through the unused `MaximalTime` umbrella.
Hamilton now imports the one declaration it actually needs directly from
`Evolution.ExtendedSolutionRegularity`; no `MaximalTime` declaration is used.
The narrowed Hamilton source check passes, and an exact source replay reports
that `ham3_noncollapse` depends only on `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.

The remaining theorem-shaped `sorry`s in this file are
`ham3_flow_exists_normalized`, `ham3_cgh_limit`, and `ham3_space_box`; each
remains theorem-level **0%**.  The unconditional HCG compactness endpoint is
therefore still **0%**, while whole-project HCG machinery is conservatively
about **60%**.

## Current state — 2026-07-09

The current Hamilton file has five theorem-shaped `sorry`s:
`ham3_short_isSolution`, `ham3_flow_exists_normalized`, `ham3_noncollapse`,
`ham3_cgh_limit`, and `ham3_space_box`.  In particular:

- `ham3_rm_control` is proved: it realizes the old rescaled curvature estimate
  on genuine `FlowMetricBall`s, using the checked parabolic norm-scaling route;
- `ham3_radius_event` and `ham3_noncollapse_of` are proved: finite maximal time
  turns `R_i t_i -> infinity` into eventual fixed-radius scale inclusion, and a
  genuine original-flow `NoLocalCollapsing` producer now implies the exact
  `Ham3Noncollapse` conclusion;
- `Ham3SourceRealizes` now requires common-time carrier inclusion, the selected
  basepoint map, and equality with the pullback of the actual
  `ham3RescaledSol` metric; both Ricci and pinching transfer predicates consume
  this same realization;
- `Ham3RmBound` and `Ham3CompactInput` retain the raw slab estimate, common
  window, kappa, and geometric noncollapse through the compactness call;
- `ham3_noncollapse` and `ham3_cgh_limit` now expose the finite maximal-time
  interval (`h0omega`, `hD`) instead of silently discarding it;
- `ham3_noncollapse` and `ham3_cgh_limit` remain genuine producer endpoints at
  **0%**; the former's remaining missing input is now precisely the analytic
  original-flow `NoLocalCollapsing` producer;
- `PointedRiemannianManifold.compact_of_ricci`, the eventual global comparison
  maps, and `limit_to_orig` are checked; `limit_to_orig` is **100%** as a
  theorem and has no `sorry`;
- `spaceForm_const_metric` is also checked; only the forward classification
  theorem `ham3_space_box` remains open in that pair.

Focused verification and the targeted `HamiltonPositiveRicci` refresh passed
after this interface tightening.  The source/compactness contract refactor is
100% checked infrastructure; it does not raise either open producer theorem
above 0%.

The whole HCG project is conservatively about **45% machinery**, while its
endpoint theorems remain **0%**.  The checked `limit_to_orig` consumer must not
be counted as progress on the still-open `ham3_cgh_limit` producer.

## Archived 2026-06-05 snapshot (superseded by the current state above)

Date: 2026-06-05

Workspace: `E:\testdifferential-geometry`

Branch: `short-time-existence`

Lean file:
`DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/HamiltonPositiveRicci.lean`

Verification:

- `lake build` completed successfully after the branch update.
- At that snapshot the Hamilton file had six theorem-shaped `sorry`s.
- `DifferentialGeometry/Geometry/Flow/RicciFlow/MaximalTime.lean` has one additional extension-criterion `sorry` that is upstream of the maximal-flow package story.

## Historical structure (2026-06-05)

This file is no longer just a statement shell.  The middle Hamilton pipeline is
substantially checked:

- scalar lower-bound package extraction: `ham3_scalar74`, `ham3_finite_time`;
- point selection from scalar blow-up: `ham3_scalar_blowup`, `ham3_point_select`;
- Section 9 Ricci nonnegativity and pinching consumers:
  `ham3_ric_nonneg9`, `ham3_rescaled_ric_nonneg`,
  `ham3_pinch9_fixed`, `ham3_pinch9`;
- Section 10 pinching estimate consumer:
  `ham3_pinch_imp_can`, `ham3_pinch_imp`;
- curvature control from nonnegative Ricci:
  `ham3_rm_bound`;
- fixed-window arithmetic:
  `ham3_r0_window`;
- limit-flow algebra after CGH data is supplied:
  `limit_scalar_nonneg`, `limit_inherit`, `limit_tf_zero_of_decay`,
  `limit_tf_zero`, `limitEinstein_of_tf0`,
  `limit_const_sec_of_einstein`, `const_pos_of_tf0`,
  `limit_const_pos`.

The important point is that the finite-dimensional 3D algebra and the static
Einstein-to-space-form computation are already checked.  The remaining work is
mostly not local tensor algebra.

## Historical 2026-06-05 `sorry` inventory

### `ham3_flow_exists_normalized`

Location: near line 490.

Role: produces the normalized maximal finite-endpoint Ricci-flow package
`Ham3FlowPackage`, including the solution, `IsSmoothSolutionOn`, initial metric
identity, and curvature blow-up.

Current repo support:

- `DeTurckShortTime.lean` has `deTurckRicci_shortTime_existence_of_closed`.
- `HamiltonDeTurckPullback.lean` has the pullback theorem route from DeTurck
  flow to Ricci flow, but it still exposes analytic hypotheses such as raw
  variational identities and an additive chain rule.
- `MaximalTime.lean` has the maximal/singularity vocabulary and checked
  consumers from the extension criterion, but `extends_of_rmBounded` remains a
  black-box global PDE theorem.

Assessment: not fillable in one local pass.  It can be advanced by building an
intermediate theorem that returns a short-time `SolutionOn` from the DeTurck
pipeline, then a separate maximal-continuation package.  Do not try to prove the
whole normalized maximal-flow setup directly inside this file.

2026-06-05 update: `HamiltonPositiveRicci.lean` now imports
`RicciFlow/ShortTimeExistence.lean` and exposes `ham3_short_exists`, a checked
adapter that cites `ricci_flow_short_time_existence` for the full raw
metric-family/chart-Gram/PDE short-time output.  This reuses the current
headline directly, but it does not close `ham3_flow_exists_normalized`: the
short-time theorem is stated for an inner-product model space, needs
`BoundarylessManifold I M`, and returns a raw metric family rather than the
canonical `SolutionOn`/`IsSmoothSolutionOn` plus normalized maximal interval and
endpoint curvature blow-up required by `Ham3FlowPackage`.

Verification passed for the Hamilton file after the adapter.  The remaining
frontier is still the maximal-continuation/package promotion, not the short-time
existence headline.

2026-06-05 exhaustive audit update: the short-time dependency surface was
source-checked around the headline and assembly/flow stack.  The active
short-time proof-body placeholders found are the DeTurck-Ricci parabolic
short-time theorem and the Weyl/on-diagonal spectral analytic input.  A direct
source-check failure in `Pullback/Defs.lean` was repaired before rechecking the
headline and Hamilton consumer.

### `ham3_noncollapse`

Location: near line 2087.

Role: turns Perelman's no-local-collapsing theorem plus curvature control on the
selected rescaled slabs into `Ham3Noncollapse P Q kappa ham3_r0`.

Current repo support:

- `Perelman/Noncollapsing.lean` defines abstract `ScaleControlledBall`,
  `KappaNoncollapsedAtBall`, and no-local-collapsing statement interfaces.
- `Ham3Noncollapse` already stores explicit small/unit ball witnesses through
  `Ham3BallPair`.
- `Ham3Noncollapse.unitVolLower` and `Ham3Noncollapse.unitNested` are checked
  projections.

Assessment: this is one of the best next targets, but not by proving Perelman's
theorem.  The tractable next step is an adapter theorem:

1. define the selected `ScaleControlledBall` family for the `r0` balls;
2. connect radius/window/curvature-control hypotheses to the abstract
   `KappaNoncollapsedAtBall`;
3. package the small/unit ball pair and volume monotonicity into
   `Ham3Noncollapse`.

That reduces `ham3_noncollapse` to the real Perelman theorem interface instead
of leaving all ball witness work inside the black box.

### `ham3_cgh_limit`

Location: near line 2107.

Role: produces `Ham3CGHLimitExists P Q` from curvature control, fixed window,
and noncollapsing.

Current repo support:

- `Ham3CGHLimitExists` already exposes the useful Section 12 output:
  subsequence, window, regularity, connected/boundaryless limit manifold,
  smooth limit flow, Ricci transfer, base scalar convergence, positive scalar,
  and pinching transfer.
- There is no concrete CGH convergence relation or approximate-isometry map
  layer in this current `DifferentialGeometry` tree comparable to the older
  `HCGCompactness` work.

Assessment: keep this as a genuine compactness black box for now.  The useful
next work is to introduce an honest CGH convergence record, not to fake the
proof.  Minimum useful fields would include pointed embeddings/diffeomorphisms
on compact exhaustion sets, smooth pullback convergence of metrics and
curvature, and explicit transfer theorems for Ricci nonnegativity, scalar base
normalization, and pinching decay.

### `limit_to_orig`

Location: near line 2643.

Role: transfers a constant-positive-sectional metric on the CGH limit manifold
back to the original manifold `M`.

Current problem:

- `Ham3CGHLimitExists` currently proves existence of a limit flow and transfer
  data, but it does not store an eventual diffeomorphism between `M` and the
  limit manifold.
- The theorem statement consumes only the current `hlimit` tuple and
  `LimitConstPosSec L`; those hypotheses do not contain enough data to build a
  metric on `M`.

Assessment: this is another good next target, but the statement needs a real
producer/interface.  The smallest honest move is to add a separate transfer
predicate, for example `Ham3LimitEventuallyDiffeomorphicToOriginal` or
`Ham3LimitConstPosSecTransfersToOriginal`, and make `limit_to_orig` a checked
consumer of that datum.  If that datum is folded into `Ham3CGHLimitExists`,
then `ham3_limit_const_metric` can stay as the main consumer.

### `ham3_space_box`

Location: near line 2755.

Role: global geometry/topology theorem: closed connected constant-positive
sectional curvature implies spherical space-form topology.

Assessment: not a local Hamilton/Ricci-flow target.  It needs a global
Riemannian topology package: universal cover, Bonnet-Myers or compactness,
space-form classification, deck group, and quotient model.  Current nearby
files have universal-cover and Bonnet-Myers-facing material, but not a direct
producer for `SphericalSpaceForm`.

### `spaceForm_const_metric`

Location: near line 2768.

Role: reverse direction: construct a constant-positive-sectional metric from a
spherical space-form quotient model.

Assessment: also global quotient-geometry work.  It may be easier than
`ham3_space_box` if one introduces a quotient Riemannian metric API for finite
free isometric quotients of the round sphere.  It is not a Lean-local theorem
from the current fields alone, because the structure does not already package a
descended smooth Riemannian metric.

## Historical 2026-06-05 work order (superseded)

Recommended order:

1. **Make `limit_to_orig` honest.**
   Add a compactness-transfer predicate or field that explicitly supplies the
   eventual diffeomorphism/pullback metric transfer from the CGH limit to `M`.
   Then turn `limit_to_orig` into a checked consumer.  This would remove one
   misleading `sorry` from the final Section 12 chain without pretending to
   prove CGH compactness.

2. **Factor `ham3_noncollapse`.**
   Add an adapter from the abstract Perelman ball vocabulary to
   `Ham3Noncollapse`.  The current `Ham3BallPair` and projections are already
   designed for this.  This makes the remaining black box exactly Perelman's
   no-local-collapsing theorem, rather than a mixed package.

3. **Split `ham3_flow_exists_normalized`.**
   Do not attempt the full global setup at once.  First target a short-time
   Ricci-flow package from the DeTurck short-time theorem and pullback theorem;
   then separately connect maximal continuation and the
   `MaximalTime.extends_of_rmBounded` extension criterion.

4. **Leave `ham3_cgh_limit` as black-box until a real CGH record exists.**
   The next productive step is interface design: maps, domains, convergence of
   pullback metrics/curvatures, and transfer lemmas.  A direct proof attempt in
   `HamiltonPositiveRicci.lean` would become a fake compactness API.

5. **Postpone `ham3_space_box` and `spaceForm_const_metric`.**
   They are global topology/quotient geometry, not the Ricci-flow endpoint
   frontier.  They should live in a separate topology/space-form layer.

## Historical next prompt (superseded)

Work in `E:\testdifferential-geometry` on
`DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/HamiltonPositiveRicci.lean`.
Do not attack the CGH compactness theorem directly.  First introduce an honest
limit-to-original transfer predicate for eventual diffeomorphism/pullback of a
constant-positive-sectional metric, then refactor `limit_to_orig` into a
checked consumer of that predicate and verify the Hamilton module.

## 2026-06-05 reschedule note: HCG-first route

The current working priority should be adjusted toward importing the old HCG
compactness work into the rescheduled `DifferentialGeometry` tree by copy/paste,
not by importing the old `RicciFlower` namespace.

### Live correction: scalar positivity

Do not overread the absence of the old name `limit_scal_pos_smp` in this file.
The current `HamiltonPositiveRicci.lean` search finds `LimitScalarPosAt`,
`LimitScalarPos`, `LimitScalarNonneg`, and checked consumers such as
`limit_scalar_nonneg` and `limit_const_pos`, but not the old symbol
`limit_scal_pos_smp`.  It may have been split, renamed, or moved during the
reschedule.  Before deciding scalar strong maximum principle work is closed,
tomorrow re-search the scalar maximum principle and limit-flow files for the
actual producer of `LimitScalarPos`.

### HCG import target

The old HCG material under
`E:\differential-geometry\RicciFlower\HCGCompactness\` should be treated as the
source to copy and adapt.  The current tree has no comparable
`HCGCompactness` folder, while `HamiltonPositiveRicci.lean` already exposes the
Section 12 consumer interface:

- `Ham3CGHLimitData`;
- `Ham3CGHLimitExists`;
- `Ham3RicNonnegTransfer`;
- `Ham3LimitBaseScalarConv`;
- `LimitScalarPos`;
- `Ham3PinchTransfer`.

The promising route is:

1. Add a current-tree HCG folder, probably under
   `DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/`, unless the
   import graph shows a better `Geometry/Compactness/` home.
2. Copy the old HCG interface files in small groups, renaming imports and
   namespaces to the current `DifferentialGeometry` layout.
3. Keep the metric compactness theorem, MSM135 Theorem 3.9, as an honest
   theorem-shaped input/interface at first.  Do not fake its proof.
4. Prove or assemble MSM135 Theorem 3.10, "Compactness for solutions", from the
   assumed 3.9 plus serious explicit inputs: pointed flow sequence data,
   derivative bounds, injectivity/noncollapse input, smooth-flow upgrade, and
   time-window bookkeeping.
5. Add a thin adapter from the 3.10 conclusion into `Ham3CGHLimitExists`.

If this route works, `ham3_cgh_limit` is no longer an opaque black box: it can
be filled by applying the 3.10 interface to the selected rescaled flows and
then forgetting the HCG conclusion down to the Hamilton Section 12 fields.  The
hard work is not the final `exact`; it is packaging the inputs and transfer
fields honestly.

### What 3.10 must provide for Hamilton

For the Hamilton endpoint, the solution compactness interface should at least
produce:

- a limit manifold and pointed smooth Ricci-flow solution on the fixed backward
  window;
- a strict subsequence selecting the rescaled flows;
- regularity on the open fixed window;
- connectedness and boundarylessness of the limit, or a separate topology
  producer;
- scalar basepoint convergence, enough to prove `LimitBaseScalarOne`;
- smooth Ricci tensor transfer, enough for `Ham3RicNonnegTransfer`;
- pinching/trace-free Ricci transfer, enough for `Ham3PinchTransfer`;
- positive scalar on regular times, or a clear scalar strong maximum principle
  producer if this is not already carried by the current rescheduled scalar
  layer.

The last four bullets are where the adapter needs care.  A generic pointed
compactness theorem will not by itself know Hamilton's normalization, Ricci
nonnegativity, or improved pinching statement.

### Noncollapse and injectivity

The current tree already has
`DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/Noncollapsing.lean` with
abstract `ScaleControlledBall`, `KappaNoncollapsedAtBall`, and no-local-
collapsing theorem interfaces.  `HamiltonPositiveRicci.lean` also has
`Ham3BallPair`, `Ham3Noncollapse`, `Ham3BallPair.nested_of_le`, and the
noncollapse consumer surface.

For the HCG route, Perelman noncollapse should eventually feed the injectivity
or noncollapse input needed by MSM135 3.10.  The immediate adapter target is not
to prove Perelman's theorem, but to connect the existing Hamilton ball witnesses
and curvature-window data to the compactness input expected by the 3.10 wrapper.

### Space-form direction: current global geometry status

Current live tree has more global geometry than the older note assumed:

- `DifferentialGeometry/Geometry/Metric/Pullback.lean` provides
  `Diffeomorph.pullbackMetric` and its inner-product evaluation.
- `DifferentialGeometry/Geometry/Curvature/PullbackNaturality.lean` provides
  `metricRm04Std_pullback`; a focused `rg` found no local `sorry` in that file.
- `DifferentialGeometry/Geometry/Topology/UniversalCover/` contains the
  universal-cover manifold, lifted metric, curvature pullback, completeness
  pullback, and fibre-equivalence layer.
- `DifferentialGeometry/Geometry/Comparison/BonnetMyers/Headlines.lean`
  contains the diameter, compactness, and finite-fundamental-group headline
  route.

But `spaceForm_const_metric` is still not a short local fill:

- there is no current `RoundSphere.lean` / `roundMetricS3` module in this tree;
- `RoundSphere3` is only an abbrev inside `HamiltonPositiveRicci.lean`;
- `SphericalSpaceFormQuotientModel` stores a finite free metric-space
  isometric action and an abstract quotient smooth structure, but not a
  descended smooth Riemannian quotient metric;
- Bonnet-Myers compactness and finite fundamental group still have explicit
  `sorryAx` caveats in `Headlines.lean`, and `UniversalCover/Manifold.lean`
  has a remaining fibre-countability/good-cover `sorry`.

So the direct construction direction should be planned as a separate
space-form/quotient geometry project:

1. build or import a round `S^3` smooth Riemannian metric and prove constant
   sectional curvature;
2. strengthen the quotient model or add an adapter carrying a descended smooth
   quotient metric from a finite free isometric action;
3. use `metricRm04Std_pullback` to pull constant positive sectional curvature
   back along the stored smooth equivalence.

The reverse direction `ham3_space_box` depends more on Bonnet-Myers,
universal-cover, deck group, and spherical-space-form classification, so it is
even less likely to be the next local theorem.

### Tomorrow's concrete first pass

1. Re-check whether `limit_scal_pos_smp` is now in a split scalar file or has
   been absorbed into current `LimitScalarPos` data.
2. Create the current-tree HCG folder and copy the smallest old files needed to
   state MSM135 3.9 and 3.10 interfaces.
3. Keep 3.9 as the honest compactness input; focus on proving the 3.10 wrapper
   shape and the adapter into `Ham3CGHLimitExists`.
4. After the adapter compiles, revisit `ham3_cgh_limit` and see whether its
   remaining inputs are exactly curvature window, noncollapse/injectivity, and
   transfer fields.
5. Separately audit `spaceForm_const_metric` against the live global geometry
   files, especially pullback curvature, universal cover, Bonnet-Myers status,
   and the missing round-sphere/quotient-metric layer.

## 2026-06-05 short-time -> SolutionOn bridge landed

Goal of this pass: advance `ham3_flow_exists_normalized` by *genuinely citing*
the short-time headline `ricci_flow_short_time_existence` (through the existing
adapter `ham3_short_exists`), packaging its raw output into a folder-level
`SolutionOn`, without hiding any gap behind a fake wrapper.

### Context change

The Hamilton global variable block was switched to an inner-product model space,
matching what the short-time headline requires:

```
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
```

(`InnerProductSpace Real E` subsumes the old `NormedSpace Real E`; `NeZero
(Module.finrank Real E)` is the dimension-positivity instance the short-time and
`ricciTensor` APIs use.)  This makes `ham3_short_exists` citable at the file's own
`E, I, M`.  `BoundarylessManifold I M` is *not* added globally: it is supplied per
theorem, either as an explicit instance binder (where the signature mentions
`ricciTensor`) or derived from `hM.2.2.1` via the Mathlib instance
`[I.Boundaryless] -> BoundarylessManifold I M`.

### New declarations (inserted right after `ham3_short_exists`)

1. `ham3_short_solution_candidate` — **CHECKED, no `sorry`.**
   The local bridge.  From `Closed3Manifold` + `g0` it cites `ham3_short_exists`
   and returns `T > 0`, a `SolutionOn (closedOpen 0 T hT)` whose
   `S.family.metric` is (definitionally) the short-time `g_fam`, the start-metric
   identity `S.family.metric (closedOpen 0 T hT).initial = g0`, and the raw
   chart-Gram smoothness (`Ioo 0 T`), chart-Gram continuity (`Ico 0 T`), and
   pointwise `∂_t g = -2 Ric` PDE restated in terms of `S.family.metric`.
   Carries `[BoundarylessManifold I M]` as a binder because the PDE clause names
   `ricciTensor`.

2. `ham3_isSolution_of_shortTimeData` — **honest frontier, `sorry`.**
   Takes a `SolutionOn (closedOpen 0 T hT)` together with *exactly* the raw
   chart-Gram smoothness/continuity and the pointwise PDE produced by (1), and
   concludes `IsSolutionOn S`.  It does **not** assume `IsSolutionOn` /
   `IsSmoothSolutionOn` or any of their fields — only the genuine analytic output
   of the short-time construction.  The `sorry` is the real remaining analytic
   gap (assembling the `IsSolutionOn` fields — metric/connection smoothness, the
   `∂_t g = -2 Ric` equation at regular interior times, and canonical
   scalar/Ricci spacetime continuity and the scalar heat equation — from the
   chart-local short-time data).  This is the single new `sorry` introduced by
   this pass.

   *Correction (same day):* the frontier targets `IsSolutionOn`, **not**
   `IsSmoothSolutionOn`.  The promotion `IsSolutionOn → IsSmoothSolutionOn` is
   already a fully *checked* producer — `smoothOfSol` in
   `RicciFlow/Regularity.lean` (no `sorry` in that file) — which derives the
   canonical scalar/Ricci regularity, coordinate inverse/Ricci evolution,
   symmetries, and the Ricci-norm Bochner/Laplacian expansion from `IsSolutionOn`
   on a boundaryless manifold.  Re-`sorry`ing that step would have been wrong;
   it is reused instead.

3. `ham3_short_smooth_solution` — checked modulo (2).
   Assembles (1), (2), and the checked `smoothOfSol`: `T > 0`, a
   `SolutionOn (closedOpen 0 T hT)` with the start-metric identity and
   `IsSmoothSolutionOn S`.  No direct `sorry`; its only gap flows through
   `ham3_isSolution_of_shortTimeData`, since `IsSolutionOn → IsSmoothSolutionOn`
   is fully proved by `smoothOfSol`.

### `ham3_flow_exists_normalized`

Now genuinely cites the headline: its body opens with
`have _hshort := ham3_short_smooth_solution (I := I) (M := M) hM g0`, so the
short-time *smooth* stage is no longer part of the `sorry`.  The remaining
`sorry` is precisely the **maximal continuation** (extend the short-time smooth
flow to a maximal normalized `[0, ω)` and assemble `Ham3FlowPackage` with
endpoint curvature blow-up).  Per the task constraint this was *not* fabricated:
`MaximalTime.lean` supplies blow-up *from* maximality
(`formsSing_of_maximal_metric`, `rmUnbounded_of_maximal`) but its
`extends_of_rmBounded` extension criterion (Black Box 11.2) is itself unproved,
so no maximal-continuation producer exists to cite.

### Verification

- `LEAN_NUM_THREADS=2 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/HamiltonPositiveRicci.lean`
  exits 0.  Only `declaration uses 'sorry'` warnings remain:
  `ham3_isSolution_of_shortTimeData` (new, intended frontier),
  `ham3_flow_exists_normalized` (pre-existing maximal-continuation gap), and the
  five pre-existing downstream `sorry`s (`ham3_noncollapse`, `ham3_cgh_limit`,
  `limit_to_orig`, `ham3_space_box`, `spaceForm_const_metric`).
- Net new `sorry`s: exactly one (`ham3_isSolution_of_shortTimeData`).
- `ham3_short_solution_candidate` and `ham3_short_smooth_solution` add no direct
  `sorry` (the latter reuses the checked `smoothOfSol` for
  `IsSolutionOn → IsSmoothSolutionOn`).
- Only `DifferentialGeometry.lean` (the aggregator) imports this file, and no
  other file references the Hamilton declarations, so the context change does not
  ripple into downstream consumers.

### Honest remaining frontier (this sub-story)

```
ricci_flow_short_time_existence   (headline, checked)
  └─ ham3_short_exists            (checked adapter)
       └─ ham3_short_solution_candidate     (checked: raw output -> SolutionOn candidate)
            └─ ham3_isSolution_of_shortTimeData   (FRONTIER sorry: raw data -> IsSolutionOn)
                 └─ smoothOfSol  (CHECKED, Regularity.lean: IsSolutionOn -> IsSmoothSolutionOn)
                      └─ ham3_short_smooth_solution          (checked modulo the frontier)
                           └─ [maximal continuation + blow-up assembly]  (still open; not in MaximalTime.lean)
                                └─ ham3_flow_exists_normalized           (sorry: maximal continuation only)
```

## 2026-06-05 live frontier recheck

Focused verification passed for both the Hamilton file and the short-time
headline file.  The Hamilton file currently has exactly seven direct
proof-body frontiers:

1. `ham3_isSolution_of_shortTimeData`: raw short-time chart-Gram/PDE data to
   `IsSolutionOn`.
2. `ham3_flow_exists_normalized`: maximal continuation and endpoint blow-up
   assembly into `Ham3FlowPackage`.
3. `ham3_noncollapse`: noncollapsing/injectivity input.
4. `ham3_cgh_limit`: Hamilton-Cheeger-Gromov limit package.
5. `limit_to_orig`: transfer from the limiting/covering/space-form metric back
   to the original manifold.
6. `ham3_space_box`: spherical space-form classification input.
7. `spaceForm_const_metric`: global space-form to constant positive metric
   conclusion.

The short-time headline still elaborates.  Its lower proof-body black boxes are
the DeTurck-Ricci parabolic short-time theorem and the Weyl/on-diagonal spectral
estimate.  No additional short-time frontier appeared in this recheck.

## 2026-06-05 adapter design prompt

Target adapter:

```lean
theorem ham3_isSolution_of_shortTimeData
    [BoundarylessManifold I M]
    {T : Real} (hT : 0 < T)
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 T hT))
    ...
    : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S
```

Feasibility check before coding: the current raw hypotheses are probably too
weak to prove the target literally.  `MetricFamilySmoothOn.coeff` asks for
`ContDiffOn Real top` on `D.carrier = Set.Ico 0 T`, while the short-time output
only records joint `C^\infty` Gram entries on `Set.Ioo 0 T` plus continuity on
`Set.Ico 0 T` and a first-order PDE.  Also `IsSolutionOn.scalarCont` is stated
as `ContinuousAt` on all `Real x M`, not only on the interval carrier.  So the
adapter should not be attacked as one tactic proof in HamiltonPositiveRicci.

Recommended Claude route:

1. First inspect `IsSolutionOn` in `Basic/Core.lean`,
   `MetricFamilySmoothOn` in `Curvature/Realized/MetricFamily.lean`, and the
   existing short-time producers in `ShortTime/SolutionC2Continuous.lean` and
   `ShortTimeAssembly/RicciFlowPdeAtZero.lean`.
2. Do not change `SolutionOn` or `IsSolutionOn` globally on the first pass.
   Instead, state the smallest honest producer lemma in the short-time layer
   whose assumptions actually imply the `IsSolutionOn` fields for the half-open
   interval.
3. If the current raw assumptions are insufficient, stop with the exact missing
   strengthened short-time output rather than adding hypotheses directly to the
   Hamilton theorem.  The likely missing package is a `ShortTimeRegularityOn`
   style producer containing carrier-local metric-family smoothness, connection
   smoothness, interval-local scalar/Ricci/Rm/nablaRic continuity, and scalar
   evolution.
4. Once that producer exists, keep `ham3_isSolution_of_shortTimeData` as a thin
   consumer: construct the `IsSolutionOn` record field by field, use the raw PDE
   only for `equation`, and use the short-time regularity producer for the
   remaining fields.
5. Only after the adapter checks, verify that `ham3_short_smooth_solution` still
   uses the checked `smoothOfSol` promotion and that `ham3_flow_exists_normalized`
   still has only the maximal-continuation frontier.

Stop condition: if the proof needs global-in-time `scalarCont` outside
`Set.Ico 0 T`, or infinite one-sided time regularity at `t = 0` not present in
the short-time theorem, report a missing API/statement-strength issue.  Do not
paper it over with a new polished hypothesis in HamiltonPositiveRicci.

## 2026-06-05 adapter feasibility audit — BLOCKED (both stop conditions hit)

Outcome of the audit: `ham3_isSolution_of_shortTimeData` is **not fillable on
this pass**.  Both stop conditions fire.  The frontier is a missing-producer /
statement-strength frontier, not a local proof-search problem.  No code beyond
an honest docstring on the frontier was changed; `IsSolutionOn`/`SolutionOn`
were not touched; no new `sorry` was introduced (net `sorry` count unchanged).
Focused verification passed.

Classification: **statement-strength (primary) + missing analytic producer
(secondary).**

Field-by-field map of `IsSolutionOn` against the short-time output
(`ham3_short_solution_candidate` gives joint chart-Gram `C∞` on `Ioo 0 T`,
chart-Gram continuity on `Ico 0 T`, and the pointwise `∂_t g = -2 Ric` on
`Ico 0 T` with the derivative taken `within Ici 0`):

- `smoothMetric.metricTensor_cont` — joint metric continuity on `Ico 0 T`:
  **reachable** from chart-Gram continuity (modulo per-chart → bundle-section
  assembly).
- `smoothConnection` — per-flow-time Levi-Civita spatial `C∞`: **reachable**,
  trivial (each fixed-time `leviCivitaConnectionOfMetric` is smooth; no time
  regularity demanded).
- `equation` — `∂_t g = -2 Ric` at regular (interior) times: **reachable** from
  the raw PDE, modulo (i) a `ricciTensor g x v w = metricRicciAt g x (vec2 v w)`
  bridge and (ii) `within Ici 0` → `within D.carrier` at interior times.
- `ricciCont` — Ricci bundle continuity on the carrier: **reachable** in
  principle from `ricci_continuous_in_metric_time` (continuity on `Icc 0 T` from
  chart data up to 2nd order), modulo per-point → joint bundle assembly.
- `rm04Cont` — `Rm` (2nd order) continuity: plausibly reachable from the `C²`
  metric-time continuity.
- `ricciNormSpace`, `ricciNormGrad` — per-time spatial: **reachable**.
- `smoothMetric.coeff` and `smoothMetric.frameCompSmooth` — **BLOCKED**: they ask
  for `ContDiffOn ⊤` / `ContMDiffOn ⊤` (`C∞`-in-time) on the closed-at-`0`
  carrier `Ico 0 T`.  The short-time layer exposes joint `C∞` only on the *open*
  `Ioo 0 T` plus `C²` up to the endpoints (`deturck_solution_c2_continuous_icc0`).
  `C∞`-up-to-`t=0` is mathematically true (parabolic smoothing from smooth data)
  but **unexposed** — only `C²` is proven.  This is the "infinite one-sided
  regularity at `t = 0`" stop condition.
- `nablaRicCont` — **BLOCKED**: needs continuity of the 3rd-order `∇Ric`; the
  short-time layer exposes chart time-continuity only up to 2nd order.
- `scalarEvolution` — **BLOCKED**: the scalar curvature heat equation
  `∂_t R = ΔR + 2|Ric|²` is a genuine evolution identity, not present in the
  short-time output.
- `scalarCont` — **HARD BLOCKER**: stated *globally* as
  `∀ p : Real × M, ContinuousAt (fun q => S.scalar q.1 q.2) p`.  A half-open
  `SolutionOn (closedOpen 0 T)` controls its metric family only on the carrier
  `Ico 0 T`; off the carrier the family is unconstrained (and Ricci-flow
  curvature can blow up at the right end), so global scalar continuity is not
  produced by — and is in general false for — short-time data.  This makes the
  current `ham3_isSolution_of_shortTimeData` statement unprovable as written,
  independent of the analytic gaps above.  Confirmed structurally: nothing in the
  tree constructs `MetricFamilySmoothOn` or `IsSolutionOn` from raw data; the
  only `IsSolutionOn` builders are `isSolutionOn_timeShift` and `paraSolution`,
  which transform an existing `IsSolutionOn`.  So the global `scalarCont` field
  has never been discharged from scratch.

Recommended redesign (for a follow-up pass that is allowed to edit `IsSolutionOn`
and the short-time layer — do not do this inside HamiltonPositiveRicci):

1. **Weaken `IsSolutionOn.scalarCont` to carrier-local**, e.g.
   `ContinuousOn (fun q : Real × M => S.scalar q.1 q.2) (D.carrier ×ˢ Set.univ)`
   (or joint continuity over `{t // t ∈ D.carrier} × M`, matching
   `Tensor0SFamilyContinuousOnSet`).  `scalarTime` is already carrier-local
   (`K ⊆ D.carrier`).  Audit and weaken the downstream consumers consistently:
   `smoothOfSol`/`scalarSTContOfSol`, `ScalarSTContOn.scalar_continuousOn`, and
   the scalar WMP consumers, all of which currently assume the global form.
2. **Add a short-time regularity producer** (`ShortTimeRegularityOn`-style, in the
   short-time/regularity layer, or by strengthening `ricci_flow_short_time_existence`'s
   exposed output) supplying the three analytic items: `C∞`-up-to-`t=0`
   metric-coefficient time regularity on `Ico 0 T` (upgrade from `C²`-on-`Icc` +
   `C∞`-on-`Ioo`); 3rd-order `∇Ric` joint continuity on the carrier; and the
   scalar heat equation at regular times.
3. Only then make `ham3_isSolution_of_shortTimeData` a thin field-by-field
   consumer.

Difficulty assessment: item 1 is a focused but cross-cutting API edit (a design
choice touching several consumers).  Item 2 contains genuine analysis (the
`C∞`-up-to-`0` upgrade and the scalar heat equation) and is the substantial
remaining mathematics.  Neither is a routine local proof, so the frontier was
left visible rather than papered over.

## 2026-06-05 carrier-local scalar continuity redesign implemented

The statement-strength part of the scalar-continuity obstruction is now fixed.
`IsSolutionOn.scalarCont`, `ScalarSTContOn`, and `CanonicalScalarRegularOn` are
carrier-local `ContinuousOn` packages over `D.carrier x M`, and
`SolutionOn.scalar_continuousOn` now requires an explicit slab-subset proof
`Set.Icc 0 T subset D.carrier`.

Direct consumers were updated rather than hidden behind new assumptions:
time-shift and parabolic-rescaling compose the carrier-local scalar continuity
through their time maps; Ricci-preservation uses subtype continuity on
`{t // t in D.carrier} x M`; scalar lower-bound and improved pinching restrict
to slabs using their existing carrier-subset hypotheses; finite-time scalar
continuity is now requested as a local family for every `T < omega`; and the
Hamilton scalar package exposes the same local family.

Verification passed for the edited scalar-continuity API and Hamilton consumer.
The actual theorem-body `sorry` count in `HamiltonPositiveRicci.lean` remains
7; no new `sorry` was introduced.  The short-time adapter remains blocked for
the genuine producer reasons from the audit: closed-at-zero `MetricFamilySmoothOn`
regularity, third-order `nablaRic` continuity, and scalar evolution.

## 2026-06-05 item-2 reshape: short-time IsSolutionOn producer

Goal of this pass: advance the `IsSolutionOn` short-time frontier ("item 2").

Investigation of the short-time / DeTurck / parabolic / spectral layers
(findings):

- C∞-up-to-`t=0` metric time regularity: NOT available.  Strongest exposed is
  `deturck_solution_c2_continuous_icc0` (`C²` on `Icc 0 T`).  The headline only
  exposes joint `C∞` on the OPEN `Ioo 0 T`.
- 3rd-order `∇Ric` carrier continuity: NOT available (only 2nd-order Ricci
  continuity, `ricci_continuous_in_metric_time`).
- Scalar heat equation: the only producer (`scalarEvolOfSmooth`) consumes
  `IsSmoothSolutionOn`, i.e. it is downstream of `IsSolutionOn` — circular for
  this purpose.  No producer derives it from the metric PDE + smoothness alone.
- No theorem anywhere CONSTRUCTS `MetricFamilySmoothOn` or `IsSolutionOn` from
  primitive data (only `timeShift`/`paraSolution` transform an existing one).

So the three gaps are genuine hard parabolic-analysis facts that this project
black-boxes by design (like short-time existence itself); "filling" them is a
major PDE-formalization effort, out of scope for an incremental pass.

Correctness defect found and fixed: the previous frontier
`ham3_isSolution_of_shortTimeData` took the raw chart-Gram/PDE data of the
candidate as hypotheses and concluded `IsSolutionOn S`.  Those hypotheses are
too weak to imply `IsSolutionOn` (they pin only the open-interval `C∞`, the
`C⁰`-up-to-`0` continuity, and the 1st time derivative; one can satisfy them yet
fail the `C∞`-up-to-`0` / heat-equation fields), so as a `∀ S` implication it is
effectively false — a `sorry` should not sit on it.

Reshape (in `HamiltonPositiveRicci.lean`):

- Removed `ham3_isSolution_of_shortTimeData`.
- Added `ham3_short_isSolution (hM) (g0) : ∃ T (hT : 0 < T) S, S.family.metric
  initial = g0 ∧ IsSolutionOn S`.  This is a `g0`-based producer about the
  *actual* short-time solution, so the statement is mathematically true; its
  scaffolding (`SolutionOn`, initial metric) is the checked
  `ham3_short_solution_candidate`, and the `IsSolutionOn` fields are a single,
  precisely-labeled parabolic-regularity `sorry` (the three facts above), matching
  how `ricci_flow_short_time_existence` itself black-boxes its deep analytic core.
- Rewired `ham3_short_smooth_solution` to `ham3_short_isSolution` + the checked
  `smoothOfSol`.

Verification passed (focused).  Net `sorry` count in
`HamiltonPositiveRicci.lean` is unchanged at 7; the item-2 frontier is now a
true, correctly-located, single labeled black box (`ham3_short_isSolution`,
the short-time parabolic regularity input) instead of an effectively-false
raw-data consumer.

Difficulty / next: genuinely discharging `ham3_short_isSolution` needs the
short-time analytic layer strengthened to expose `C∞`-up-to-`0` metric
regularity and 3rd-order `∇Ric` continuity, plus a non-circular scalar-heat
producer (derive `ScalarEvolutionEquationOn` from `∂_t g = -2 Ric` + smoothness,
not from `IsSmoothSolutionOn`).  These are PDE-analysis tasks in the short-time /
Evolution layer, not local proofs.

## 2026-06-05 weakening execution — IN PROGRESS (tree mid-refactor)

Executing the `MetricFamilySmoothOn` weakening (interior-`C∞` + carrier-continuity).
The audit confirmed it is sound, but execution exposed a larger-than-expected
blast radius:

Done & checked in isolation:
- `RealTimeInterval` gained `regular_isOpen : IsOpen regular` (TimeInterval.lean),
  with all 11 builders updated.  Needed because `coordMetricSmoothAt`/
  `coordInvSmoothAt` produce `ContMDiffAt` at regular times, which needs a
  *neighbourhood*; `D.regular` only provides one when open.  TimeInterval.lean
  checks green.
- `MetricFamilySmoothOn` weakened: `coeff`/`frameCompSmooth` moved to `D.regular`,
  new `coeff_cont` (carrier continuity).  MetricFamily.lean checks green.

Edited, not yet re-verified against the new struct:
- Core.lean `isSolutionOn_timeShift.smoothMetric` (4-field rebuild).
- Evolution/Metric/Basic.lean `coordMetricSmooth`→`D.regular`, `coordMetricSmoothAt`
  uses `regular_isOpen`.
- Evolution/Metric/InverseSmooth.lean coordinate chain → `D.regular`,
  `coordInvSmoothAt` uses `regular_isOpen`.

Remaining (the genuinely new mathematics):
- **Carrier-continuity sub-chain** for `Estimate.lean`'s `ricciNorm_coordCont`
  (which needs `ricciNorm` continuity up to `t = 0`, hence `coordInv` continuity
  up to `0`).  `coordInvSmooth` is now interior-only, so a carrier-continuity
  route is required: `coordMetricCont` (from `metricTensor_cont` via
  `eval_continuous`) → Gram continuity → **inverse continuity** (continuity of
  `ContinuousLinearMap.inverse` at invertible points) → `coordInvCont`.  This is
  ~4 new lemmas, the inverse-continuity being the nontrivial one (mirrors the
  existing smooth `coordFrameGInvCLM_spacetimeSmooth` but with `ContinuousAt`).
- `RicciPreservation.lean` 3697/3714: `.coeff.continuousOn` → `.coeff_cont`.
- `ParabolicRescaling.lean`: para interval builder `regular_isOpen`; metric
  family builder provide `coeff_cont` + move to `D.regular`.
- Full `lake-locked build` to verify the cascade.

Status: tree is mid-refactor (broken until the above land).  Claim tokens held.

## 2026-06-06 weakening COMPLETE (coordInvContOn proved, no net new sorry)

The `MetricFamilySmoothOn` weakening is finished and verified.

- Full `lake-locked build` of the whole project passed (exit 0) with the
  weakening in place.
- The hidden `D.carrier`-baked helper `contMDiffOn_finset_sum` (InverseSmooth.lean)
  was generalized to an arbitrary set `t` (backward-compatible).
- The one carrier-continuity frontier introduced by the weakening,
  `coordInvContOn` (coordinate inverse-metric continuity up to `t = 0`), is now
  **fully proved** — no `sorry`.  Its chain, all the continuity twins of the
  existing smooth lemmas:
  * `coordMetricContOn` (Evolution/Metric/Basic.lean): frame metric components
    continuous up to `0`, from `metricTensor_cont` via
    `Tensor0SFamilyContinuousOnSet.eval_continuous` + `metricTensorField_apply`;
  * `coordFrameGramCLM_contOn`, `coordFrameGInvCLM_contOn`, `coordInvContOn`
    (InverseSmooth.lean): Gram continuity → inverse continuity (via
    `ContinuousLinearMap.inverse` continuous at invertible points, reusing
    `frameGramCLM_isInvertible_at` + `coordInvCLM_eq`) → entry continuity.

Net effect of the whole weakening: **zero new `sorry`s**.  `IsSolutionOn` /
`MetricFamilySmoothOn` no longer demand the spurious `C∞`-up-to-`t=0` time
regularity (only interior `C∞` + carrier continuity), matching what short-time
existence actually provides and what consumers actually use.  The added
`RealTimeInterval.regular_isOpen` field is a sound, contained improvement.

This unblocks (does not yet fill) `ham3_short_isSolution`: its `smoothMetric`
obligation is now satisfiable from short-time data; the remaining genuine
short-time analytic content for that frontier is `nablaRicCont` (3rd-order ∇Ric
continuity) and the scalar heat equation.

## 2026-06-06 nablaRicCont weakened to interior (verified, exit 0)

Continued the weakening from `MetricFamilySmoothOn` to the `∇Ric` continuity
field.  Audit confirmed `IsSolutionOn.nablaRicCont` is **never consumed up to
`t = 0`**: the only extractor `nablaRicFamilyContinuousOnSet` has no call sites,
and every other use is a transport rebuild (`isSolutionOn_timeShift`,
`paraSolution`) or the `ricciRegOfSol` pass-through.  `∇Ric` is a ≤3rd-order
differential expression in the metric, so interior `C∞` already supplies it.

Edits: `IsSolutionOn.nablaRicCont`, `CanonicalRicciRegularOn.nablaRic_cont`, and
`nablaRicFamilyContinuousOnSet` changed `3 D.carrier` → `3 D.regular`; the two
transport rebuilds updated to `MapsTo … regular`.  Full `lake-locked build`
passed (**exit 0**); claim tokens released.

Net: `IsSolutionOn`'s regularity surface now matches exactly what is consumed —
interior `C∞` + carrier `C⁰` for the metric, carrier `C⁰` for the ≤2nd-order
curvature, interior `C⁰` for 3rd-order `∇Ric`.  No spurious up-to-`0` demand
remains anywhere.

## 2026-06-06 CORRECTION: the scalar heat equation is already proven in-tree

Earlier notes listed "the scalar heat equation" as remaining content of
`ham3_short_isSolution`.  That is **wrong** — it is fully formalized and
sorry-free:

- Intrinsic field form: `IsSolutionOn.scalarEvolution` (Basic/Core.lean:555),
  `∂ₜ R = Δ_g R + 2‖Ric‖²`.
- Proven derivation: `scalarEvolutionEquationOn_of_ricciEvolution`
  (Evolution/Scalar/Assembly.lean:88) from the Ricci evolution; the
  contracted-Bianchi reduction `2ΔR − 2Q + 2‖Ric‖² ⟿ ΔR + 2‖Ric‖²` is
  `scalarEvolutionEquationOn_of_contractedBianchi` (Evolution/Scalar/Basic.lean:82).
- The Ricci evolution it rests on is also proven: `coordRicciEvol`
  (Evolution/Ricci/CoordinateIdentities.lean:876), from Christoffel evolution +
  ∇² commutators.  **The entire `Evolution/{Scalar,Ricci,Connection}` subtree is
  sorry-free.**

So the scalar evolution is the *best-supported* `IsSolutionOn` field, not a gap.
The genuine residual of `ham3_short_isSolution` is **regularity packaging only**:
wiring the candidate's chart-Gram smoothness/continuity into the intrinsic
continuity fields and citing the proven `coordRicciEvol` →
`scalarEvolutionEquationOn_of_ricciEvolution` chain for `scalarEvolution`.  The
single genuinely black-boxed analytic input is upstream:
`deturck_ricci_flow_parabolic_short_time_existence`
(ShortTime/DeTurckRicciPde.lean:128) + the conjugating-flow field regularity
(ShortTimeFlow/ConjugatingFlowProperties.lean:3954).

## 2026-06-06 sorry structure of the final theorem `thm_2_1`

`thm_2_1` = `ham3_main`: closed connected 3-manifold with `AdmitsPosRicci`
⟹ `AdmitsConstPosSec ∧ SphericalSpaceForm`.  Forks into the analysis branch
`ham3_const_metric` and the topology branch `ham3_equiv`.

The Section 7–9 differential-geometric core is **proved** (finite-time, scalar
blow-up, point selection, parabolic rescaling, Ricci-nonneg preservation,
pinching estimates, Rm bound, and the whole `limit_*` tensor-transfer chain to
`limit_const_pos`).  Remaining `sorry`s, grouped:

1. Short-time existence (upstream PDE): `deturck_…_short_time_existence`,
   `ConjugatingFlowProperties.lean:3954`; bridge `ham3_short_isSolution`
   (HamiltonPositiveRicci.lean:571, now regularity packaging only).
2. Maximal continuation: `ham3_flow_exists_normalized` (:628); the input
   `extends_of_rmBounded` (MaximalTime.lean:159, Black Box 11.2) exists but is
   currently *bypassed* (`formsSing_of_maximal_metric`/`rmUnbounded_of_maximal`
   appear only in a docstring, not in any proof body).
3. Singularity/convergence: `ham3_noncollapse` (:2288, Perelman noncollapsing),
   `ham3_cgh_limit` (:2310, Hamilton compactness), `limit_to_orig` (:2844).
4. Topology endpoint: `ham3_space_box` (:2944), `spaceForm_const_metric` (:2956).

## 2026-06-06 scalarEvolution: assumed field → derived theorem (DONE, exit 0)

The scalar-curvature heat equation is no longer a black-boxed structure field.
`IsSolutionOn.scalarEvolution` was **removed as a field** and replaced by a
sorry-free derivation, so `ham3_short_isSolution` no longer assumes it.

New file `Evolution/Scalar/IntrinsicDerivation.lean` (sorry-free):

- `coordNab2Ric_eq_nabla2RicField` — the explicit coordinate-frame `∇²Ric`
  (`extDeriv − Γ` formula) equals the abstract bundled `totalNabla0SFun³` of
  Ricci, via `nabla0SFun_apply_selfChart_slots` + the `ext0S_basis`
  agree-on-a-basis principle.  (The repo already had `coordNab2Can` proving the
  same crux — the explicit↔abstract bridge was NOT missing, contrary to an
  earlier over-pessimistic read.)
- `scalarLaplacianTraceInFrame_coord_eq_laplacianAt` — the **diffusion bridge**:
  `gⁱʲgᵏˡ∇²Ricᵢⱼₖₗ = ΔR` (`laplacianAt`).  Assembled from `nabla2Trace02`
  (Hessian-trace commutation, `∇g=0`), `scalarLap_smooth` (laplacian = trace of
  Hessian), `metricTracePair0SAt_eq_sum_basis`, and the sum-swap
  `scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace`.
- `scalarEvolution_of_isSolution` — derives the EXACT former field statement
  `∂ₜR = ΔR + 2|Ric|²` from `hS : IsSolutionOn`, by running the proven frame-form
  chain `scalarEvolutionEquationOn_of_ricciEvolution` (∂ₜg⁻¹ = 2Ric° via
  `coordInvEvol`, ∂ₜRic Lichnerowicz via `coordRicciEvol`, curvature
  trace/symmetry) and applying the three frame→intrinsic bridges (scalar trace,
  diffusion, reaction) plus a `G`-congruence to `flowG`.

Integration:
- `IsSolutionOn` lost its `scalarEvolution` field (`Basic/Core.lean`); the unused
  `scalarEvolAt` and the two transport constructions (`timeShift` in `Core`,
  `paraSolution` in `ParabolicRescaling`) dropped it.
- `scalarEvolOfSol` (`Regularity.lean`) reroutes to `scalarEvolution_of_isSolution`
  (gains `[I.Boundaryless]`; its sole caller `smoothOfSol` already carries it, so
  no further propagation).  `IsSmoothSolutionOn.scalarEvolution` is a *separate*
  field and is untouched.
- Full `lake-locked build` **exit 0**, no new `sorry`.

Net: the scalar evolution is now mathematically grounded end-to-end — the
frame-form heat equation (already in `Evolution/Scalar`) plus the realization
identity `ΔR = gⁱʲgᵏˡ∇²Ricᵢⱼₖₗ`.  `ham3_short_isSolution`'s residual is purely the
remaining regularity-packaging fields, never the scalar PDE.

## 2026-06-06 Bernstein–Bando–Shi derivative estimates (toward `extends_of_rmBounded`)

Goal: fill `extends_of_rmBounded` (`MaximalTime.lean:159`, Black Box 11.2 — the
maximal-continuation extension criterion) by formalizing the global BBS
derivative estimates (Chow–Knopf *The Ricci Flow: An Introduction*, Theorem 7.1,
the compact-manifold / global-maximum-principle case — no Shi cutoffs needed).

**BBS core — COMPLETE, sorry-free, full `lake-locked build` exit 0 (9847 jobs),
`#print axioms` clean (no `sorryAx`):**

- `Evolution/BernsteinShi.lean` — Stage 1: upper-bound scalar maximum principle
  `scalar_subsolution_affine_bound` (`(∂ₜ−Δ)F ≤ b`, `F(0)≤a` ⟹ `F ≤ a+bt`), the
  `|∇Rm|²` heat predicate `NablaRm04NormHeatBoundOn`, and the `m=1` Bernstein
  estimate `bernstein_first_derivative_estimate` (`F = t|∇Rm|²+β|Rm|²`).
- `Evolution/BernsteinShiHigher.lean` — Stage 2: the **general-`m`**
  `G`-quantity induction `BernsteinTower.estimate` /`estimate_div`
  (`|∇ᵐRm|² ≤ towerConst²·K²/tᵐ`, all `m`), via eqs 7.4–7.6 (the telescoping
  `Wterms_nonpos` + `scalar_subsolution_affine_bound`).  Parametric in the
  `BernsteinTower` structure (the tower of heat inequalities).
- `Evolution/RiemannNormHeatProducer.lean` — Stage 3a (`k=0`): `|Rm|²` heat
  equation for a solution + `|reaction| ≤ 16·card⁶·|Rm|³` (Lemma 7.4), from the
  Uhlenbeck curvature evolution.
- `Evolution/NablaRiemannHeat.lean` — Stage 3b (`k=1`): `|∇Rm|²` heat bound
  (eq 7.2/14.17) + the general-`k` `∗`-reaction bound `abs_nablaRmReactionMulti_le`
  in the `towerReactionSum` shape.
- `Evolution/IteratedNablaRmTower.lean` — the variable-rank `∇ᵏRm` tower bridge
  (Route A, no dependent-type issues): `iteratedRmComp` (rank-`(4+k)` component
  recursion), the general orthonormal reduction `multiNormInFrame_eq_compNormSqMulti`,
  and the producer `iteratedRmTower_heatBound : IteratedRmTowerOn → TowerHeatBoundOn`.

The reusable lever throughout is the `A∗B` convention: evolution stated as
*inequalities* with norm-product bounds `Σ|∇ʲRm||∇^{k−j}Rm||∇ᵏRm|`, never exact
reaction tensors (the producers leave the raw Uhlenbeck/Bochner/commutator
component facts as hypotheses, matching the existing `|Ric|²` architecture).

**In progress (final two pieces):**
- All-`m` BBS for a real solution (`BernsteinShiSolution.lean`): instantiate the
  `BernsteinTower` per-`m` from the tower bridge (uniform constant via the
  "zero above `m`" truncation), apply `estimate_div`.
- Stage 4 (`CinftyLimitGlue.lean`): `C^∞` limit `g(t)→g(ω)` from the BBS bounds
  + restart short-time + smooth glue ⟹ the single-endpoint extension; then wire
  into `extends_of_rmBounded`.  (No Ricci-flow uniqueness needed — that is only
  for the maximal-flow *construction*, a separate gap.)

## 2026-06-06 k=1 ∇Rm evolution: EQUATION derived; BBS bound is the framework frontier

Goal (user-authorized): genuinely ground the `k=1` `IteratedRmTowerOn.heatEq`
(the `∇Rm` tensor evolution) from Ricci-flow/Uhlenbeck geometry, rather than
leave it an assumed interface field.  Outcome: **the `k=1` evolution EQUATION is
fully derived** (the residual `(∂ₜ−Δ)(∇Rm)` is now *identified* as curvature
actions, not assumed); **the BBS quantitative *bound* `|reaction| ≤ C|Rm||∇Rm|`
is blocked on four framework-level gaps** and is the documented frontier.

**Equation — DONE, all sorry-free, `#print axioms` clean (no `sorryAx`):**

- `Evolution/RmRealizationBridge.lean` — the rank-`(0,4)/(0,5)` realization
  bridge (the crux), mirroring `coordNab2Ric_eq_nabla2RicField`.  Bundled fields
  `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field` (`totalNabla0S` of
  `S.base.rm04`); the rank-uniform step bridge `covDerivStepComp_frameComp_eq`;
  `iteratedRmComp_one_eq_nablaRm04Field` (neighbourhood) /
  `iteratedRmComp_two_eq_nabla2Rm04Field` (centre); and the **discharged**
  `Nabla20SRealizesAt` packages → `rm04_ricciIdentityAt` (s=4) /
  `nablaRm04_ricciIdentityAt` (s=5), making the general `(0,s)` Ricci identity
  `tensor0S_ricciIdentity_of_torsionFree` (`Tensor/RicciIdentity/Tensor0S/Formula.lean:975`)
  genuinely applicable to `Rm`/`∇Rm`.  Witnesses come from `totalNabla0S_realizes`,
  never assumed.
- `Evolution/NablaRiemannCommutator.lean` (spatial) — `nablaLapComm_orthonormalTrace`:
  `Δ(∇Rm)(c) − ∇(ΔRm)(c) = Σ_a nablaLapCommReactionTerm(a,a,c)`, from the `(0,5)`
  Ricci identity + telescoping (the `[Δ,∇]` commutator is **derived**).
- `Evolution/NablaRiemannTimeDeriv.lean` (temporal) —
  `iteratedRmComp_one_hasDerivWithinAt`: `∂ₜ(∇Rm) = ∇(∂ₜRm) − (∂ₜΓ)∗Rm` in the
  `MultiLevelTimeDerivOn` shape, from the `extDeriv`/`∂ₜ` swap +
  `evol_christoffel_inFrame` (`∂ₜΓ`) + Uhlenbeck (`∂ₜRm`) as cited shapes.
- `Evolution/NablaRiemannCommutatorBound.lean` —
  `nablaLapComm_T1_eq_covDeriv_curvatureAction` (the slot-swap/∇ commutation,
  proved concretely via `eval_smooth_slots`) and
  `nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction`: the
  full `k=1` reaction exhibited as `∇(curvatureAction(Rm)) + curvatureAction(∇Rm)`
  (`= ∇(Rm∗Rm) + Rm∗∇Rm`).

So `(∂ₜ−Δ)(∇Rm)` is genuinely the curvature reaction — the **equation half of
`heatEq` is grounded for `k=1`**.

**Bound — the frontier.**  `|reaction| ≤ C|Rm||∇Rm|` (the BBS Cauchy–Schwarz step)
is blocked on four *framework-level* gaps (confirmed by three independent agents,
each via a different route — none is a single lemma):

1. The inverse metric is `InverseMetricComponents : M → Idx → Idx → ℝ` (a
   frame-component function), **not** a bundled `(2,0)` tensor — so `∇g⁻¹=0`
   cannot even be *stated* in the `totalNabla0S` framework.
2. `Rm13 = raise(Rm04)` is unavailable — `metricRm13`/`metricRm04` are produced
   independently; raising-parallelism is proven only at rank `(0,2)`, never `(1,3)`.
3. `∇Rm13` does not exist — no `totalNablaRS` realization for the `(1,3)` curvature.
4. Frame mismatch — `nablaLapCommReactionTerm` lives in `coordinateFrameAt` (not
   orthonormal at its centre), while the norms require an orthonormal frame.

Closing it is a major framework project (bundled inverse metric `+∇g⁻¹=0`; the
`(1,3)` raising equivalence `+`parallelism; `∇Rm13` via `totalNablaRS`;
coordinate↔orthonormal reconciliation) — reusable for all-`k` but disproportionate
to one estimate.  **Decision (user): bank the genuine equation; the bound stays
the documented frontier; the BBS estimates remain parametric in `IteratedRmTowerOn`.**

Routes that informed this (all genuine reports, no fakes): route 1 — bridge the
bundled `tensorCov` `[Δ,∇]` (`frame_trace_thirdCovDeriv_swap`) to components: no
bridge exists from that representation.  Route 2 — rework producers to the bundled
level: the tree has **no time derivative of a bundled tensor section at all**.
Route 3 — the `(0,s)` Ricci identity in the realization rep: found
`tensor0S_ricciIdentity_of_torsionFree`, which **enabled route 4** (the bridge
above).  The `k=1` bound's three attempts (field-level, orthonormal/concrete,
rm04-contraction) all converged on the four gaps above.

**Consolidation (2026-06-06):** full `lake-locked build` → **exit 0 (9847 jobs)**.
All new `k=1` modules — `RmRealizationBridge`, `NablaRiemannCommutator`,
`NablaRiemannTimeDeriv`, `NablaRiemannCommutatorBound` — plus the earlier BBS
stack (`MultiNormHeat`, `BernsteinShi`/`BernsteinShiHigher`/`BernsteinShiSolution`,
`RiemannNormHeatProducer`, `NablaRiemannHeat`, `IteratedNablaRmTower`,
`CinftyLimitGlue`) coexist green and sorry-free.  The only `sorry`s remaining in
the tree are the pre-existing main-theorem frontier items
(`HamiltonPositiveRicci.lean`: `ham3_flow_exists_normalized`, `ham3_noncollapse`,
`ham3_cgh_limit`, `limit_to_orig`, `ham3_space_box`, `spaceForm_const_metric`) and
a few in unrelated files (`UniversalCover`, `Exterior`).  Net new `sorry`s from all
of the BBS / `k=1` work: **zero**.

## 2026-06-07 session-end: k=1 spatial reaction bound CLOSED + roadmap

**Done + independently verified:** the `k=1` quantitative SPATIAL reaction bound
`|nablaLapCommReactionTerm| ≤ C·|Rm|·|∇Rm|` is genuinely closed
(`Evolution/NablaRiemannReactionBound.lean`, `#print axioms` =
`[propext, Classical.choice, Quot.sound]` on all four headline theorems, no `sorry`,
full `lake-locked build` EXIT 0 / 9860 jobs).  **All four framework gaps** that six
prior agents had declared blocking are resolved (see `Evolution/IteratedNablaRmTower.md`
follow-ups 1–10 for per-piece detail).  New banked, axiom-clean files:
`RmRaisingBridge`, `NablaRiemannOrthoFrame`, `Tensor/RSTensor/ContractionLeibniz`,
`RmFrozenSlotField`, `Geometry/Operator/CotangentSharpSmooth`,
`NablaRiemannCommutator(+Bound)`, `NablaRiemannTimeDeriv`, `NablaRiemannT2Bound`,
`NablaRiemannReactionBound`.

**Roadmap — to close `extends_of_rmBounded` (the BBS pillar):**
1. **Full `k=1` producer** `nablaRm04NormHeatBoundOn_of_components` for a solution.
   Spatial input is done; remaining = the **time-derivative assembly**: instantiate
   `iteratedRmComp_one_hasDerivWithinAt`'s `hrm`/`hchr`/`hswap` from the solution
   (Uhlenbeck `∂ₜRm`, `evol_christoffel_inFrame` `∂ₜΓ`, the time/spatial swap) + the
   `MultiNormHeat` Bochner norm-square step.  *[MEDIUM — instantiating existing shapes.]*
2. **All-`k` producer** (discharge `IteratedRmTowerOn` for a solution at every `k`):
   generalize the `k=1` spatial+time work to all `k` (rank-uniform `[Δ,∇]∇ᵏRm` + the
   `∇ʲRm ∗ ∇^{k−j}Rm` reaction bound).  The primitives and the pattern now exist.  *[LARGE.]*
3. **BBS bounds**: `BernsteinShiSolution` (done, parametric) instantiated with (2) →
   all-`m` `|∇ᵏRm| ≤ Cₘ K / t^{m/2}` for a solution.
4. **`C^∞` convergence** (`CinftyLimitData`/`CinftyGlueData`, Stage 4's labelled
   interface): Arzelà–Ascoli from the BBS bounds → the smooth limit metric `g(ω)`.
   *[MEDIUM–LARGE, genuine analysis.]*
5. **Wire** `ricci_flow_extends_construction` (Stage 4, done Route B) + (4) →
   `extends_of_rmBounded` (`MaximalTime.lean:159`).  *[MEDIUM.]*

**Then for the full theorem** (`thm_2_1` / `ham3_flow_exists_normalized`):
`extends_of_rmBounded` (above) **plus** the still-open convergence/compactness pillar —
`ham3_noncollapse` (Perelman κ-noncollapsing), `ham3_cgh_limit` (Cheeger–Gromov
compactness), `limit_to_orig`, `ham3_space_box`, `spaceForm_const_metric` — a comparably
large body of work, largely untouched.  Foundation: the short-time-existence (DeTurck)
`sorryAx` remains the standing black box.

**Next concrete step:** the `k=1` time-derivative assembly (roadmap step 1).

## 2026-06-07 consolidation: generic Bochner stack + all-k heat equation landed

The `k=1` "three framework walls" dead-end was dissolved — the walls were over-counts
(`∇g⁻¹=0`, the frame change, the covariant Leibniz were all present/buildable). The
user's `∂ₜ‖T‖²` abstraction was the lever: it cascaded into a complete **general
norm-square Bochner machinery** and the **all-k heat equation**.

**New verified modules** (each `lake-locked build` EXIT 0, no `sorry`, `#print axioms`
= `[propext, Classical.choice, Quot.sound]`):
- `Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean` — general `∂ₜ‖T‖²`
  (`hasDerivWithinAt_normSq0S`; flow form `…_ricciFlow` = `Ric∗T² + 2⟨∂ₜT,T⟩`).
- `…/Tensor0SInnerLeibniz.lean` — the covariant inner-product Leibniz `inner0S_nabla`
  (`∇⟨T,S⟩=⟨∇T,S⟩+⟨T,∇S⟩`) — the recurring "covariant Leibniz" wall, resolved generically.
- `…/Tensor0SBochnerSplit.lean` + `…/Tensor0SBochnerProduct.lean` — the general Bochner
  Laplacian split `tensorNormBochnerSplit_mc` (`Δ‖T‖²=2⟨ΔT,T⟩+2‖∇T‖²`, hypothesis-free
  via `hess_norm0S`).
- `Evolution/NablaRiemannHeatFrameInvariant.lean` — `abs_spatialCommNablaRm_intrinsic_le`
  (frame-independent k=1 spatial reaction bound) + `compNormSqMulti_orthoBasis_eq_normSq0S`.
- `Evolution/NablaRiemannHeatSolution.lean` — the `horth`-free producer
  `nablaRm04NormHeatBoundOn_scalar`.
- `Evolution/NablaRiemannHeatFull.lean` — `nablaRm04NormHeatEquationOn_intrinsic`
  (k=1 heat equation DERIVED from the two Bochner lemmas — was always a raw input).
- `Evolution/RmRealizationBridgeAllK.lean` — rank-uniform bridge
  `iteratedRmComp_eq_nablaKRm04Field` + `nablaKRm04_ricciIdentityAt` ((0,4+k) Ricci id, all k).
- `Evolution/IteratedRmTowerHeatEq.lean` — `nablaKRm04NormHeatEquationOn_intrinsic`
  (**all-k** heat equation `∂ₜ|∇ᵏRm|²=Δ|∇ᵏRm|²−2|∇^{k+1}Rm|²+reaction`) +
  `iteratedRmComp_hasDerivWithinAt` (rank-uniform `∂ₜ∇ᵏRm`).
- `Evolution/IteratedRmTowerProducer.lean` — reaction-form bridge
  `nablaKRm04Reaction_orthoBasis_eq_compContract` (concrete reaction = `2⟨combinedStar,∇ᵏRm⟩`
  in a g-orthonormal basis; inverse-metric mismatch closed; Ricci half a genuine bounded
  `j=0` factor).

**Precise remaining frontier** to discharge `IteratedRmTowerOn.heatEq` → BBS bounds →
`extends_of_rmBounded` (a GENUINE wall, carefully verified — not an over-count):
1. **All-k iterated commuted-curvature identity** `(∂ₜ−Δ)∇ᵏRm = Σⱼ ∇ʲRm∗∇^{k−j}Rm` — the
   BBS eq-7.5/7.6 higher-order induction. `j=0`/`j=k` boundary terms come from
   `nablaKRm04_ricciIdentityAt` + `inner0S_nabla`; the **`0<j<k` cross terms** (iterated
   `[Δ,∇ᵏ]Rm`) are assembled only at `k=1` (~2500-LOC `T₁`/`T₂`). This is the hard core.
2. **`∂ₜ∇ᵏRm`** (component time derivative, Lemma 6.1): banked `∂ₜRm13`+realization+lowering,
   unblocked but unbuilt.
3. **Frame reconciliation**: clean-`∂ₜ` `iteratedRmComp_hasDerivWithinAt` is in
   time-independent `coordinateFrameAt`; the reaction collapse needs the `g(t)`-orthonormal basis.

Pillar B (convergence/compactness: `ham3_noncollapse`, `ham3_cgh_limit`, …) and the DeTurck
short-time `sorryAx` remain as before. Per-piece detail: `Evolution/IteratedNablaRmTower.md`
follow-ups #1–15.

**Resume:** frontier #1 (the all-k iterated commutator) is the genuine remaining mathematics
— generalize the `k=1` `T₁`/`T₂` machinery to all ranks via the rank-uniform `(0,s)` Ricci
identity + `inner0S_nabla` applied iteratively.

## 2026-06-13 ham3_short_isSolution: scoped frontier (NOT pure packaging — a real analytic wall)

User picked the `ham3_short_isSolution` direction expecting "regularity packaging only".
A deeper feasibility pass corrects that: the residual is NOT purely mechanical assembly.
It bottoms out on a genuine analytic fact the short-time/DeTurck layer does not provide.

### Field-by-field map of `IsSolutionOn S` (Core.lean:508) against the candidate

The candidate (`ham3_short_solution_candidate`) exposes, for the canonical trivialization
frame at each `x0`: chart-Gram **joint** C∞ on `Ioo 0 T ×ˢ baseSet`, chart-Gram **joint**
C⁰ on `Ico 0 T ×ˢ baseSet`, and the 1st-order PDE `∂ₜg = -2 Ric` (`HasDerivWithinAt … Ici 0`).

REACHABLE (direct from candidate + small bridges):
- `smoothConnection` — each fixed-time LC connection is smooth; no time regularity demanded.
- `equation` — from the raw PDE: `Ici 0`→`carrier` at interior `t`, + the
  `ricciTensor g x v w = S.ricciAt t x (vec2 v w)` bridge.
- `smoothMetric.coeff` (`ContDiffOn ⊤ … D.regular = Ioo 0 T`) — from chart-Gram joint C∞ on
  `Ioo`; the fixed-vector inner product is a constant-coefficient combination of Gram entries.
- `smoothMetric.coeff_cont` (`ContinuousOn … D.carrier = Ico 0 T`) — from chart-Gram joint C⁰.
- `smoothMetric.frameCompSmooth` — joint C∞ on `Ioo ×ˢ u` for the canonical frame; arbitrary
  `IsLocalFrameOn` frame via the time-independent transition functions.
- `ricciNormSpace`, `ricciNormGrad`, `scalarTime` — fixed-time spatial regularity from the
  fixed-time smooth metric.

BLOCKED — the curvature **bundle joint-continuity** fields:
- `smoothMetric.metricTensor_cont` : `Tensor0SFamilyContinuousOnSet 2 D.carrier (metric)`
- `ricciCont` : `Tensor0SFamilyContinuousOnSet 2 D.carrier (S.ricci)`
- `rm04Cont`  : `Tensor0SFamilyContinuousOnSet 4 D.carrier (S.base.rm04)`
- `nablaRicCont` : `Tensor0SFamilyContinuousOnSet 3 D.regular (∇Ric)`  (interior only)
- `scalarCont` : `ContinuousOn (scalar) (D.carrier ×ˢ univ)`

### Two keystones (both genuinely missing)

**Keystone A — component→section continuity constructor (missing API, buildable).**
`Tensor0SFamilyContinuousOnSet` (MetricFamily.lean:252) is *joint* total-space continuity
over `{t∈K}×M`. The tree has only the EVAL direction (`eval_continuous`,
`TensorMultilinear.continuous_section_apply_base`: section→component) and an algebra
(`mono`/`comp_time`/`add`/`smul`). There is **no constructor** that builds a
`Tensor0SFamilyContinuousOnSet` FROM joint local-frame/chart component continuity — the
continuity analog of `contMDiffOn_iff_localFrame_coeff`. Every existing instance is a
transport rebuild (`timeShift`/`paraSolution`). Route: `FiberBundle.continuousAt_totalSpace`
(already used by `add`/`smul`) + the `Tensor0SModel` trivialization-fiber-coordinate ⟷
component bridge. Moderate bundle-trivialization work. Layer: `Curvature/Realized/` (or a new
`Tensor0SContinuityFromComponents` file). With Keystone A the candidate's **joint** chart-Gram
C⁰ on `Ico` discharges `metricTensor_cont` (hence the whole `smoothMetric` field).

**Keystone B — joint (t,x) curvature continuity UP TO t=0 (genuine analytic wall).**
`ricciCont`/`rm04Cont`/`scalarCont` are on `D.carrier` (up to t=0) and are genuinely consumed
there: the tensor/scalar maximum principle (`RicciPreservation.lean`) and the HCG whole-window
bounds (`AllTimesBoundsFlow.lean:466`) use closed slabs `[0,T]`/`uIcc` *including* the initial
time, so these fields CANNOT be weakened to `D.regular` (unlike `nablaRicCont`, which is
interior). But the DeTurck layer (`ShortTime/SolutionC2Continuous.lean`
`deturck_solution_c2_continuous_icc0`; `ShortTimeAssembly/RicciContinuityInMetricTime.lean`
`ricci_continuous_in_metric_time`/`ricci_gfam_continuous_on`) proves curvature continuity up
to t=0 only **per-fixed-x in time** — never **jointly in (t,x)**. On the interior `Ioo 0 T`
joint C∞ is available, so the interior `nablaRicCont` is fine; the wall is exactly the
**joint, up-to-t=0** continuity of `Ric`/`Rm`/`R` on the carrier. This needs (i) the short-time
headline `ricci_flow_short_time_existence` STRENGTHENED to expose the joint C²-up-to-0 chart-Gram
data (`hC2_chart` shape, jointly in (s,y)), currently hidden, and (ii) a genuine
joint-continuity-of-curvature analytic proof from it. This is statement-strength + missing
analytic producer, NOT assembly.

### Verdict / classification

`ham3_short_isSolution` is NOT fillable this pass. Classification: missing API (Keystone A) +
missing analytic producer & statement-strength (Keystone B). Per CLAUDE.md the wall is left
visible rather than papered over with Hamilton-level hypotheses or a faked bundle constructor.

Recommended brick order (independent sessions):
1. Keystone A: the component→section `Tensor0SFamilyContinuousOnSet` constructor (reusable;
   needed by ALL bundle-continuity work, incl. future HCG eq 3.3/3.4). Discharges `smoothMetric`.
2. Short-time output strengthening: expose joint C²-up-to-0 chart-Gram from the DeTurck layer
   in `ricci_flow_short_time_existence`'s headline (the data already exists internally as the
   `hC2_chart` hypothesis to `deturck_solution_c2_continuous_icc0`).
3. Keystone B: joint (t,x) curvature continuity up to t=0 from (2) + Keystone A → `ricciCont`,
   `rm04Cont`, `scalarCont`. Genuine analysis.
4. Assemble all 9 `IsSolutionOn` fields → fill `ham3_short_isSolution`. Note the whole chain
   still rests on the standing DeTurck `sorryAx`, so even a filled `ham3_short_isSolution` is
   NOT axiom-clean — it removes the *intermediate* `sorry`, not the foundational black box.

## 2026-06-13 CORRECTION (user): Keystone B is NOT a wall — recenter into the open interval

User correction (accepted): the "joint continuity up to t=0" I called a genuine analytic wall
is dissolved by the standard recentering trick. The solution is jointly C∞ on the OPEN `(0,T)`
(exposed). Restrict to a CLOSED interior slab `[a,b] ⊂ (0,T)` (`0 < a < b < T`): every
carrier-continuity field then only needs continuity at points INTERIOR to `(0,T)`, where the
flow is already jointly smooth — there is no up-to-`t=0` limit to take. So `IsSolutionOn` on an
interior slab follows from the exposed joint C∞ alone, with NO joint-up-to-0 proof and NO
short-time-headline strengthening. Brick steps 2 (headline strengthening) and 3 (Keystone B)
above are therefore UNNECESSARY for the smooth-solution producer.

Architectural consequence (the only real residue): the interior-slab solution's initial slice
is `g(a)`, not `g0`. This is exactly the smooth-solution input the maximal-flow / blow-up
analysis consumes; the `g(0)=g0` initial condition is carried separately at the C⁰ level
(`metric 0 = g0` is exposed, `g→g0` continuously). The literal `ham3_short_isSolution` as stated
([0,T) + full up-to-0 `IsSolutionOn`) is the only thing still touching the rough initial instant;
the substance moves to an interior-slab producer
`isSolutionOn_interior_slab : 0 < a → a < b → b < T → IsSolutionOn (S | [a,b])`, then the downstream
maximal continuation feeds on that + the C⁰ initial condition.

### Revised SOLE missing piece: Keystone A only

`Tensor0SFamilyContinuousOnSet s K A` (MetricFamily.lean:252) = joint `{t∈K}×M` total-space
continuity. Needed for `metricTensor_cont`/`ricciCont`/`rm04Cont`/`nablaRicCont`/`scalarCont`,
all on an interior slab where joint C∞ holds. Must build a constructor:

  `Tensor0SFamilyContinuousOnSet s K A` FROM joint (t,x) continuity of the trivialization-frame
  components of `A`, via `FiberBundle.continuousAt_totalSpace` (base continuous + fiber-coord
  continuous). Template: the existing `Tensor0SFamilyContinuousOnSet.add`/`const_smul` proofs
  (MetricFamily.lean:324–356) already use `FiberBundle.continuousAt_totalSpace` and manipulate
  the `.2` fiber coordinate as a continuous map — same pattern, but constructing rather than
  transforming. The fiber coordinate of `Tensor0SModel s ℝ E` ↔ `component0S`/chart-Gram bridge
  is the bookkeeping. Mathlib `contMDiffOn_iff_localFrame_coeff` (`VectorBundle/LocalFrame.lean`)
  is the single-base SMOOTH analog (at n=0 = continuity) — usable for the per-fixed-t section but
  the joint (t,x) version needs `continuousAt_totalSpace` directly.

  NOTE: `metricTensor_cont` is NEVER constructed from scratch in-tree (only transported via
  `timeShift`/`paraSolution`), so there is no existing template for the constructor — it is
  genuinely new bundle infrastructure. Size: a focused file (~150–300 LOC), moderate
  trivialization difficulty. Home: new sibling `Geometry/Curvature/Realized/` file importing
  `MetricFamily.lean`, or appended into `MetricFamily.lean`.

  Once Keystone A exists: feed it the joint chart-Gram C∞ (`chartGramMatrix_entry_contMDiffOn`
  + the joint short-time smoothness on `Ioo`) for the metric, and the curvature analog for
  `Ric`/`Rm` (curvature is a smooth function of the jointly-smooth metric jet on the interior),
  to discharge all five bundle-continuity fields on the interior slab.

## 2026-06-13 KEYSTONE A DONE (verified, exit 0, no sorry)

New file `Geometry/Curvature/Realized/MetricFamilyContinuity.lean`:
`tensor0SFamilyContinuousOnSet_of_chartComp` — the component→section bundle-continuity
constructor. From: for every trivialization centre `x₀` and multi-index `idx`, joint continuity
(on the trivialization domain `{q | q.2 ∈ baseSet x₀}`) of
`q ↦ A q.1.1 q.2 (fun k => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q.2 (chartModelBasis (idx k)))`,
it produces `Tensor0SFamilyContinuousOnSet s K A`.

Proof (verified): `FiberBundle.continuousAt_totalSpace` reduces section continuity at `q₀` to
base continuity (`continuous_snd`) + fibre-coordinate continuity; fibre coord
`= A.compContinuousLinearMap (symmL …)` (rfl); `eval0SCLE` (finite-dim eval homeomorphism,
`DifferentialGeometry.Analysis.Parabolic.TensorSpectral`) turns fibre-coord continuity into
per-component continuity (`continuousAt_pi` + `eval0SCLE_apply` + `compContinuousLinearMap_apply`);
each component is exactly the supplied `hcomp`, restricted to the open nbhd of `q₀`.

Setting: stated in `InnerProductSpace Real E` (NOT `MetricFamily.lean`'s `NormedSpace` section) —
`chartModelBasis`/`eval0SCLE` need the Euclidean structure, and putting it in `MetricFamily.lean`
caused a `NormedSpace` instance diamond. All realized Ricci-flow consumers are in `InnerProductSpace`.

METRIC CONSUMER ALSO DONE (verified, exit 0, no sorry, same file):
`metricTensorCont_of_chartGram` — from joint chart-Gram continuity (per centre `x₀`, entries
`q ↦ chartGramMatrix (g q.1.1) x₀ q.2 i j` continuous on the trivialization domain) produces
`Tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g t) x)`. Proof: apply the
keystone; reduce the component via `metricTensorField_apply` + `chartGramMatrix_apply`, with
`symmL ℝ q.2 (chartModelBasis (idx k)) = chartBasisVecFiber x₀ (idx k) q.2` closing by `rfl`
(symmL's `toFun` is `e.symm`, and `chartBasisVecFiber := e.symm · (chartModelBasis ·)`). This is
the `metricTensor_cont` field of `MetricFamilySmoothOn` / `IsSolutionOn`, done.

REMAINING BRICKS (clearly scoped, each self-contained; increasingly couple to the short-time
family structure in `ShortTimeExistence`/`HamiltonPositiveRicci`):
1. SMOOTH analog of the keystone — `…ContMDiff…_of_chartComp` (joint `ContMDiffOn` of the section
   on `D.regular ×ˢ u` from joint chart-Gram C∞). Then `coeff` (ContDiffOn-in-time) and
   `frameCompSmooth` (arbitrary `IsLocalFrameOn`) follow by evaluating the smooth section against
   smooth frame fields (`contMDiff_section_apply_gen`, already in `BundleSmoothEvalRealized`).
   `coeff_cont` follows from the continuity consumer just built.
2. Assemble `MetricFamilySmoothOn` for the short-time family on an interior slab (recentered) from
   (1) + the done `metricTensor_cont`. `smoothConnection`: each fixed-time Levi-Civita is smooth.
3. `equation` field: from the short-time first-order PDE (`Ici 0` → `D.carrier` at interior t,
   + the `ricciTensor g x v w = ricciAt`-bridge).
4. Ricci/Rm/scalar bundle continuity (`ricciCont`/`rm04Cont`/`scalarCont`) on the interior slab:
   curvature is a smooth function of the jointly-smooth metric jet; feed the SMOOTH-keystone the
   curvature-component joint smoothness, OR the continuity keystone the curvature-component joint
   continuity. `ricciNormSpace`/`ricciNormGrad`: fixed-time spatial from the fixed-time metric.
5. `isSolutionOn_interior_slab : 0<a → a<b → b<T → IsSolutionOn (S | [a,b])` assembling 1–4.
6. Bridge to `ham3_short_isSolution` ([0,T)+g0) via recentering + the C⁰ initial condition, OR
   restate the downstream maximal-flow consumer to take the interior-slab producer.

## 2026-06-13 DE-RISK: brick 4 (ricciCont/rm04Cont) is ALREADY built, not a wall

`ShortTimeAssembly/RicciContinuityInMetricTime.lean` contains a full `RicciContJointAux`
namespace with JOINT `(t,x)` curvature continuity: `jointRicci_continuousOn` (:740),
`jointRiemann_continuousOn` (:701) — joint `ContinuousOn (fun q : ℝ×M => chartRicciTensor
(g_DT q.1) α i k (extChartAt α q.2)) Sp` from joint chart-Gram `iteratedFDeriv` (k≤2)
continuity — plus `moving_chartCoord_jointContinuousWithinAt` (:817).  So `ricciCont`/`rm04Cont`
are ASSEMBLY: short-time joint C∞ ⟶ joint `h0/h1/h2` jets ⟶ `jointRicci_continuousOn` ⟶ bridge
`chartRicci → S.ricci` chart-frame components ⟶ `tensor0SFamilyContinuousOnSet_of_chartBasisComp`
(new, verified) ⟶ `ricciCont`.  No analytic wall remains in the `ham3_short_isSolution` chain;
the rest is consumer assembly coupling to the short-time family / `SolutionOn` structure.

VERIFIED this session (all exit 0, no sorry):
- `Geometry/Curvature/Realized/MetricFamilyContinuity.lean` (NEW):
  `tensor0SFamilyContinuousOnSet_of_chartComp` (keystone), `…_of_chartBasisComp` (clean interface),
  `metricTensorCont_of_chartGram` (the `metricTensor_cont` consumer).
- `ShortTimeAssembly/RicciContinuityInMetricTime.lean` (+3 public lemmas): `chartRicci_jointContinuousOn`,
  `chartRiemann_jointContinuousOn` — expose the file-private joint `(t,x)` curvature continuity
  (`RicciContJointAux.jointRicci/Riemann_continuousOn`); and `ricciChartFrameComp_jointContinuousOn`
  (needs `[I.Boundaryless]`) — joint continuity of `ricciTensor (g_DT q.1) q.2 (cbvf α i q.2)(cbvf α j q.2)`,
  via `ricciTensor_chartBasisVec_alpha_eq` (`ricci on chart frame = chartRicci`) `.congr`'d through
  `chartRicci_jointContinuousOn`. THIS IS THE FORM `…_of_chartBasisComp` consumes for `ricciCont`.

REMAINING for `ricciCont` (steps (b)+(c) now DONE = `ricciChartFrameComp_jointContinuousOn`):
(a) short-time joint chart-Gram jets `h0/h1/h2` on the interior slab — bridge the candidate's
    `ContMDiffOn (chartGramMatrix …)` to `iteratedFDeriv (chartGramOnE …)` joint continuity
    (the only genuinely short-time-coupled, fiddly step);
(a') subtype glue: `ricciChartFrameComp_jointContinuousOn` lives over `ℝ×M` on `Sp` (good-set);
    `…_of_chartBasisComp` wants `{t∈K}×M` on `{q | q.2 ∈ baseSet}` — convert via the subtype
    inclusion + goodSet⊆baseSet, with `Sp = (image of K) ×ˢ goodSet`;
(d) `S.ricci`'s apply lemma (`S.ricci t x v = ricciTensor (g t) x (v 0)(v 1)`, Core.lean) so the
    keystone's `A = S.ricci` components match `ricciChartFrameComp_jointContinuousOn`'s output;
(e) `tensor0SFamilyContinuousOnSet_of_chartBasisComp` → `ricciCont`.
`rm04Cont`: analogous with the `(0,4)` chart-frame Riemann bridge (build the `rm04` analog of
`ricciChartFrameComp_jointContinuousOn` from `chartRiemann_jointContinuousOn` + the lowered-Rm
chart-frame identity).  Couples to `Core.lean` + short-time candidate; a focused session.

## 2026-06-13 ROOT BLOCKER for `ham3_short_isSolution`: `frameCompSmooth` is UNCONSTRUCTIBLE as stated

(Found while executing Dispatch B in `MaximalTime.md`, which is the same `chartGram → IsSolutionOn`
problem on a shifted interval. Full write-up: `MaximalTime.md` "2026-06-13 EXECUTOR — Dispatch B".)

The de-risking above (bricks 1–6, "no analytic wall remains") MISSED a field-design wall. The
`smoothMetric` field's `MetricFamilySmoothOn.frameCompSmooth` (`MetricFamily.lean:495`) requires, for
EVERY `IsLocalFrameOn I E 1 frame u` (a merely **C¹** frame — Mathlib `IsLocalFrameOn _ _ k` = each
section is `Cᵏ`), that `(g p.1).inner p.2 (frame i)(frame j)` be jointly **C∞** (`⊤`) on
`D.regular ×ˢ u`. This is mathematically FALSE for arbitrary C¹ frames (C¹-not-C² frame ⇒ C¹-not-C²
output), for ANY metric. So the field is consumable-but-not-constructible: `hS.smoothMetric.frameCompSmooth`
(an ASSUMED field) feeds consumers fine (they all pass C∞ `e.localFrame b`), but you cannot INHABIT it
when building a fresh `MetricFamilySmoothOn`. THIS is why `ham3_short_isSolution` (and Dispatch B's
sorry #4) cannot be filled — not the curvature continuity, which is genuinely assembly.

Smallest honest fix = a DESIGN DECISION (foundational structure + consumers; needs user approval):
strengthen the field's frame hypothesis `IsLocalFrameOn I E 1` → `IsLocalFrameOn I E ⊤` (C∞). Then the
field is constructible from chart-Gram C∞, and brick 1 (the SMOOTH-keystone route) goes through. Caveat:
frame-BUILDERS that currently make `IsLocalFrameOn I E 1` (`Regularity.lean:323`,
`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean:378,831`) must build `⊤`-frames (mechanical — their
underlying `e.localFrame b` is C∞). Until this is decided, treat `ham3_short_isSolution`'s `smoothMetric`
as blocked-on-design, not blocked-on-proof.

## 2026-06-19 comment cleanup

Moved stale lesson-style source comments out of
`HamiltonPositiveRicci.lean`.  The Lean comments now state only the local
interface role of each theorem/definition; the durable status notes remain here.

Lessons preserved from the source comments:

- `ham3_short_isSolution` is the short-time candidate-to-`IsSolutionOn` handoff.
  Older source comments described this as a pure parabolic-regularity black box,
  but the current note above records the sharper blocker: `frameCompSmooth` is
  not constructible as stated for arbitrary `C¹` local frames.  Treat this as a
  package/design issue until the smooth-frame hypothesis is fixed or an
  equivalent constructible field is introduced.
- `ham3_flow_exists_normalized` should continue to cite
  `ham3_short_smooth_solution` explicitly.  The source theorem remains the
  normalized maximal-continuation endpoint: build the maximal interval starting
  at `0`, package the smooth solution, and read off the endpoint blow-up.
  `MaximalTime.lean` supplies consumers from maximality, but not the full
  continuation producer.
- `Ham3Noncollapse` records small/unit ball witnesses and volume monotonicity.
  The real geodesic-ball producer should eventually prove that monotonicity
  from metric ball inclusion and Riemannian volume monotonicity; the source
  definition should not carry that implementation lesson inline.
- `ham3_scalar74` is now the checked Section 11/7 scalar-package extraction
  from `Ham3FlowPackage`, not a remaining source-code frontier.  The historical
  frontier was to identify the maximal interval with `[0, omega)`, choose the
  scalar trace and its Laplacian/Ricci-norm data, and supply scalar evolution,
  WMP regularity, the Laplacian realization, and the 3D Ricci-norm lower bound.
- `limit_ric_nonneg` and `limit_tf_decay` are now consumers of explicit CGH
  transfer packages.  The actual producer work is to construct
  `Ham3RicNonnegTransfer` and `Ham3PinchTransfer` from smooth pointed
  convergence, pullback of Ricci/trace-free data, the rescaled improved
  pinching estimate, and scalar positivity on compact limit sets.
- `limit_const_sec_of_einstein` and `const_pos_of_tf0` are checked static
  three-dimensional algebra/geometric steps, not live source-code frontiers.
  The proof route uses the static Schur/Bianchi package to make the Einstein
  factor constant, then the 3D Riemann-from-Ricci component bridge in the
  project slot convention.

Verification: focused checking passed for this cleanup pass.  The only
diagnostics were the existing theorem-shaped `sorry` warnings in this file.

## 2026-07-09 real noncollapse migration

The Hamilton-side noncollapse package now uses the canonical geometric API in
`Perelman/Noncollapsing.lean`:

- `ham3RescaledSol` is the actual `paraSolution` at the selected point-time and
  scalar-curvature scale;
- `ham3RescaledZero` records time zero as a member of that rescaled interval;
- `ham3RescaledBall` is the genuine intrinsic time-zero metric ball centered at
  `Q.point i`;
- `Ham3Noncollapse` asks for `IsRmControlled` and
  `IsKappaNoncollapsed` on those balls.

The abstract `Ham3BallPair`, its arbitrary real-valued volume fields, and the
`unitVolLower`/`unitNested` projection wrappers were deleted.  The focused file
check passed.  The new `ham3_rm_control` theorem is checked and realizes the
parabolic curvature bound on these actual balls.

The full scale bridge is now checked in `Perelman/ScaleTransfer.lean`:
distance-defined ball carriers, volume, curvature control, kappa lower bounds,
and below-scale/nonlocal predicates transfer both ways.  The checked
`ham3_radius_event` derives the needed eventual scale inclusion, and
`ham3_noncollapse_of` proves the exact Hamilton conclusion from a canonical
`NoLocalCollapsing P.S rho` input.  Thus this downstream adapter is 100%; the
theorem `ham3_noncollapse` itself remains 0% because the analytic Perelman
producer is still absent.  Its W-route machinery is about 10%, and the broader
Hamilton Section 12 endpoint remains 0%.

## 2026-07-09 CGH retention and `limit_to_orig` repair

`Ham3CGHLimitData` now retains the actual source sequence, composed original
index map, `SmoothCGHConverges` witness (hence its spatial comparison maps),
source-to-`M` diffeomorphisms, and completeness of every carrier-time limit
slice.  Primitive limit manifold/instance fields were retained so the existing
tensor proofs continue to use definitionally identical instances.

The static Einstein argument now produces `LimitRoundAt`: the exact flow slice,
a positive Ricci lower bound, and constant positive sectional curvature.
`LimitConstPosSec` remains only as a compatibility projection.  The repaired
`limit_to_orig` no longer takes unused `P`, `Q`, or an unrelated conjunction;
it consumes the exact carrier time, connectedness, boundarylessness, and
`LimitRoundAt`, while the record supplies completeness and the real CGH maps.

The data-retention refactor is 100%.  The Bonnet--Myers compactness step and
eventual-global-map API now live in `HCGCompactness/PointedConvergenceGlobal.lean`,
and `limit_to_orig` is checked with no `sorry` (**theorem 100%**).  The source
producer `ham3_cgh_limit` remains **0%**, so the whole Hamilton Section 12
endpoint remains **0%** despite this completed consumer.
