# StepDLimitMetrics.lean notes

## State (2026-07-09)

The D1-to-D2 topological realization is implemented and verified, with no new `sorry`:

- `ballOpen` and `ballStep` define the open metric-ball factors and restricted adjacent maps.
- `ballSystem` assembles source/image-controlled partial diffeomorphisms with
  `SmoothSeqSystem.ofSucc`.
- `ballSystemOfData` derives the source and image control from one-step
  `BookApproxIsoPartialData`, basepoint preservation, and
  `sqrt (1 + epsilon_j) * r_j < r_(j+1)`.
- `directedBallSystem` consumes the eventual D1 conclusion by fixing
  `epsilon = 1/2`, `p = 0`, `l = 1`, selecting a tail index, and returning the resulting smooth
  ball system as dependent data.
- `ballPullbackMetric` is the genuine Riemannian pullback on a source open, with
  `ballPullback_inner` giving its ambient differential formula.
- `ballPullback_covNorm` identifies its intrinsic covariant norm with the D1 witness-field norm;
  `ballPullback_cov_le` closes every positive-order bound available at the current start index.
- `speed_ge_of_c0`, `ballPullback_lower`, `ballPullback_upper`, and
  `ballPullback_zero_le` provide the pointwise lower/upper equivalence and order-zero bound from
  `c0_small`.
- `ballTransSource`, `nestedBallPullback`, and `ballPullback_trans` identify a composite partial
  pullback with the nested pullback through a fixed prefix and a tail.
- `ballPullback_congr` transports this equality across pointwise-equal partial maps.
- `prefixTail_cov_le` transports every positive-order tail bound unchanged when the reference
  metric is the prefix pullback; `chainPrefix_cov_le` rewrites it to the associated full-chain
  metric.
- `chain_image_ball` supplies the image carrier for every positive-length `(1/2,0)` prefix.

All of these declarations passed focused verification without new `sorry`.

This closes the previously implicit realization gap between `directed_of_b1`-shaped data and the
abstract direct-limit manifold API. It does not yet construct the limiting stage metrics.

## 2026-07-09: D2a fixed-stage limits complete

The per-order-reference route is now checked end to end. New zero-order prefix transport,
target-index cast/source bridges, and `chainPullback_bdd` prove the exact `hbdd` and `hlow` inputs
for the real fixed-stage pullback sequence. `exists_chain_limit` consumes the checked
`metricCInf_refs` endpoint and produces a smooth `C^∞`-on-compacts limit on the source ball.
`exists_chain_data` derives the required fixed-start and positive-prefix tail packages from the
original eventual directed-approximation hypothesis after one initial shift.

Focused verification passed without warnings or new `sorry`. D2a is complete. The next target is
D2b: choose one diagonal subsequence working for every stage and prove the book's `lbl407` uniform
closeness estimate. D2c will then pass the adjacent pullback identity to the stage limits to obtain
the metric cocycle.

Rejected routes:

1. Exact pullback invariance alone does not close the old `hbdd`, because its reference metric
   changes with `r`.
2. `lemma45_corII` is not a generic reference-change bound: it couples metric equivalence and
   background-metric derivative smallness under one `eps <= 1`.

The latest focused check of this file passed. Shared targeted builds remain slow because many
other agents are rebuilding the same import graph.

## 2026-07-09: D2b common diagonal and `lbl407` complete

`exists_limits_diag` now chooses one target-index subsequence for every source stage; stage
`j₀+n` uses tail length `φ k - (j₀+n)`, so all sufficiently late terms land at the same target.
The scalar feasibility layer (`limitRefFactor`, `exists_refDelta`) proves that one positive `δ`
simultaneously controls metric equivalence and every finite-order Corollary-II loss.
`diffNorm_limit_le` then changes the reference from the stage metric to the limit metric.

`exists_limits_close` combines these pieces and proves the full all-tail form of `lbl407`: for
every `ε>0` and order `p`, every sufficiently late source stage is `ε`-close to its limit for all
tail lengths and all orders through `p`. Focused verification passed without warnings or new
`sorry`. Route failures remain 2/3. The next target is D2c, the adjacent limit-metric cocycle.

## 2026-07-09: D2c adjacent metric cocycle complete

`chain_image_open` exposes the strict open-ball image control already present in the old
closed-ball proof. `chainPullback_step` proves exact adjacent-stage finite-chain alignment using
`ballPullback_assoc`, `ballPullback_trans`, and `opensMap_mfderiv`. The common diagonal then makes
the two scalar inner-product sequences eventually equal. `metricCInf_inner` and Hausdorff limit
uniqueness give the pointwise pullback cocycle for `gInf n` and `gInf (n+1)`.

`exists_limits_close` now returns convergence, the full all-tail `lbl407` estimate, and the
adjacent metric cocycle. Focused verification passed without warnings or new `sorry`. Route
failures remain 2/3. The next target is D4b in `StepDLimit.lean`.

## 2026-07-09: D2d and subtype-target D4c complete

`chainBallSystem` packages the shifted open stages and one-step restricted chain maps as a
`SmoothSeqSystem`. `chainMetricCocycle` combines the adjacent identity returned by
`exists_limits_close` with `SmoothSeqSystem.MetricCocycle.ofSucc`, so the full tangent-level metric
cocycle is checked. `tail_derivSup_lt` upgrades pointwise all-tail `lbl407` to the compact supremum
bound required by the convergence API.

`chainCGConverges` now chooses tail length `l = 0` and applies `limitCGConverges`. Focused
verification passed. This proves Cheeger--Gromov convergence for the sequence whose carriers are
the open-ball subtypes `U n`.

## Route error 3/3: endpoint targets are ambient manifolds

The subtype-target result is not yet the `MetricCompactnessConclusion X` convergence field. The
endpoint requires comparison maps into the original carriers `X.obj (subseq n).M`, with target open
set `U n`; `chainCGConverges` instead has codomain carrier `U n` and target `Set.univ`.

The smallest repair is not a new estimate. Add a smooth lift of a partial diffeomorphism through
the open embedding `U n -> M n` (the topological engine is
`OpenPartialHomeomorph.lift_openEmbedding`), package ambient-target comparison maps, and prove
`chainPullbackSeq ... 0 = g.restrictOpen U` before transporting the existing seminorm proof. This
is a routine-to-medium missing API/packaging task, not a mathematical obstruction. Recount stop
condition: 3/3.

## 2026-07-09: ambient-target D4c complete

The previous carrier blocker is closed. `PartialDiffeomorph.liftTargetOpen` lifts a comparison map
from an open subtype to its ambient manifold while keeping the source and making the target exactly
the underlying open set. `liftOpen_mfderiv` supplies the differential readout, and
`chainPullback_zero` identifies the zeroth chain metric with the ambient metric restriction.

`chainAmbientSeq` and `chainAmbientMaps` package the original ambient carriers.
`ambientCGConverges` proves the abstract direct-limit convergence statement, and
`chainAmbientConv` consumes the existing all-tail estimate at length zero. Focused verification
passed without new `sorry`. The new route-error recount is 0/3. The next target is D6
reindex/endpoint assembly.

## 2026-07-09: shrunk tail geometry and 3/3 recount stop

The D6 audit showed that the large D2 stages of radius `2^(j0+n)` cannot also provide the compact
nesting needed by completeness: their one-step image estimate consumes the full next-stage radius.
The book-faithful repair is a second, shrunk tail family with ambient radius `2^n`.

The following reusable bricks are implemented and focused-check green, with no new `sorry`:

- `tailBallOpen`, `tailBall_nonempty`, `tailBall_source`, and `tailBall_image` define the shrunk
  stages and prove that all chain maps are defined there and preserve the next shrunk stage.
- `tailClosed_image` uses the intermediate radius `(3/2) * 2^n` and the positive shift `1 <= j0`
  to put the image of the closed `2^n` ball strictly inside the next open `2^(n+1)` ball.
- `tailBallSystem` packages the shrunk stages as a `SmoothSeqSystem`.
- `tailSystem_compact` proves that each successor map has image contained in a compact subset of
  the next shrunk stage when the ambient members are proper.

The restarted route count reached its stop condition:

1. Per-stage properness is false for the open stages and cannot discharge D5.
2. The original large stages have no radius margin for compact containment; shrinking is required.
3. Relative compactness of successive images alone does not imply completeness of the union. An
   increasing relatively compact open exhaustion can still have an incomplete union, as for an
   exhaustion of an open interval.

Therefore the concrete D5 frontier is still the metric-exhaustion producer: finite limit-metric
balls must lie in a stage range. The next mathematically viable target is a quantitative
distance-to-stage-boundary lemma using the `gInf` versus ambient-metric lower bound and the radii
`2^n`; only after that gate should the existing large-stage metrics be restricted or rebuilt on
the shrunk tail system. Do not restart the diagonal D2 construction before this gate is settled.

## 2026-07-09: D5 metric exhaustion complete

The consultant's feasibility route is now implemented through the concrete exhaustion producer.
The large-stage metrics are restricted to the shrunk stages by `tailMetric`, and
`tailMetricCocycle` transports the existing cocycle without rerunning D2. The order-zero
`half_ambient_le_tail` comparison uses `lbl407` only at `p = q = l = 0`.

Compact half-radius cores are supplied by `tailCore`; `incl_mem_coreInt` and
`frontier_core_radius` identify their interior and frontier. The generic `exists_first_exit`
lemma in `StepDLimit.lean`, the factor-two `pathELength_val_le` estimate, and
`path_escape_core` give escape cost `2^n / 4`. `mem_core_of_edist`,
`baseRange_exhausts`, `finiteRange_exhausts`, and `tailRangeExhausts` then prove that every
finite Riemannian ball about any limit point lies in a shrunk-stage range.

Focused verification passed with no new `sorry`. Two unavoidable section-variable linter
warnings remain because Lean rejects omitting the elaboration-time `IsManifold (infinity + 1)`
instance even though the generated theorem does not retain it. Fresh route-error count: 0/3.

`tailLimitComplete` now combines `tailRangeExhausts`, `tailSystem_compact`,
`compactCover_of_step`, and `limitComplete_cover`. It is the concrete D5 completeness theorem,
not another conditional consumer.

Overall accounting: concrete D5 completeness theorem: 100%; its dedicated machinery: 100%.
Step D assembly/D6: 0%. Whole Step D machinery: about 96%. Next target: D6 reindex and endpoint
assembly, including threading the D1 fixed-order data and the D2 common diagonal into the shrunk
tail output consumed by `tailLimitComplete`.

## 2026-07-09: connectivity producer and D6 data alignment

The only non-geometric input still exposed by `tailLimitComplete` was stage
preconnectedness.  `tailBall_preconn` now derives it from the Riemannian metric:
for a point in a positive-radius ball, choose a path shorter than the radius and
use distance bounded by every prefix length to keep the path in the ball.  An
isolated Mathlib check of this argument passed.  `tailRangeExhausts` and
`tailLimitComplete` now install these instances internally.

For D6, `exists_chain_data` now chooses a positive start index, while
`exists_limits_diag` and `exists_limits_close` expose `1 <= j₀` and the
fixed-order `D₀` family already selected internally.  This is the exact input
shape consumed by `tailLimitComplete`; no second diagonal or incompatible choice
is needed.

Integrated verification is currently blocked before this file is elaborated.
The upstream module
`Tensor/RSTensor/NablaOnTensors/Regularity/Derivation.lean` times out while
elaborating `nablaRSFun_eval_moving_raw` at `whnf`; increasing the diagnostic
heartbeat budget to one million did not pass.  The later unknown-constant error
is a cascade from that failed declaration.  This is a performance/verification
blocker, not a mathematical Step-D route failure.  Fresh route count remains
0/3.

Final D6 theorem: 0%, because it is still unstated and unproved.  Dedicated D6
machinery: about 15%.  Whole Step-D machinery: about 96%.  After upstream
verification is restored, the next target is the flat nested-open restriction
lemma for `metricDerivNorm`; it will transport `lbl407` from the large stages to
`tailMetric`, allowing ambient CG convergence and D5 completeness to use the
same direct-limit object.

## 2026-07-10: shrunk-tail ambient convergence checked

The upstream artifact is restored.  `metricDerivNorm_flat` now transports the
pointwise derivative norm through the flat nested-open restriction used by
`tailMetric`.  `tailFlatSup_lt` consumes this bridge and the `l = 0` case of
`lbl407` to prove compact-supremum convergence on every shrunk tail stage.

`tailAmbientConv` feeds that estimate to `ambientCGConverges`.  Its limit is
definitionally the same `tailBallSystem` / `tailMetric` / `tailMetricCocycle`
object used by `tailLimitComplete`; D6 no longer needs to identify two separately
constructed limits.  Focused verification passed without warnings and no new
`sorry` was introduced.  The two existential data binders that do not occur in
later result types were renamed `_D₀`, removing the prior local linter warnings
without changing the returned tuple.

Fresh route-error count remains 0/3.  Final D6 theorem: 0% because it is still
unstated and unproved.  Dedicated D6 wiring: about 30%.  Whole Step-D machinery:
about 97%.  Next target: inspect the live
`MetricCompactnessInputs.metricCompactness` fields, then compose the Step A and
D2 subsequences/reindexing with this common convergence/completeness output.

`tailCenter_map` is also checked: transporting the stage-zero center through
the shrunk system gives the stored center at every stage.  This is consumed by
`StepDAssembly.tailMemberMaps`; the remaining alignment blocker is convergence
data indexed by the full maps record, documented in `StepDAssembly.md`.
