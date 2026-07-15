# MetricCompactnessInputs notes

## 2026-07-08

Added `MetricCompactnessInputs.ofUniformVolume`, a small constructor that
keeps the public conditional endpoint bundle in the existing
`VolumeComparisonInput` consumer shape while accepting the more explicit
`UniformBallPack` producer data from `VolumeComparisonBridge.lean`.

This is infrastructure, not a theorem discharge. The conditional Theorem 3.9
endpoint `metricCompactness` is still 0% proved because its Steps A-D assembly
is still the `sorry`. The volume-comparison theorem from the original sequence
hypotheses is also 0% proved: no Bishop-Gromov or equivalent uniform-volume
producer from `SeqBoundedGeometry` has been formalized. Its dedicated
local-volume/packing machinery is now about 75%: the generic packing
cardinality gate is checked, the explicit uniform input is checked, and this
bundle constructor is checked.

Verification passed. The existing `metricCompactness` endpoint `sorry` remains
unchanged.

Next target: either formalize the real Bishop-Gromov producer that supplies
`UniformBallPack`, or keep `UniformBallPack` as the explicit book-external
volume-comparison input and continue with the Ch4 Steps B/C/D assembly.

## 2026-07-08 joint-cap correction

Updated the bundle compatibility field from the old `lambda[0] <= r0` shape to
`stepA_cap_le`: the maximum of the Step A ratios `4` and
`50 * exp(C * 20 * lambda[0])`, multiplied by `lambda[0]`, is bounded by the
producer cap.  This is exactly what the two Step A `ballMult` consumers need
after `VolumeComparisonInput` was corrected to the joint cap `m * r <= r0`.

`ofUniformVolume` now asks for this stronger cap compatibility.  Verification
passed through the targeted `MetricCompactnessInputs` module.  The endpoint
`metricCompactness` `sorry` remains unchanged.

Added checked projection lemmas `cap_four`, `cap_four_of_nonneg`, and
`cap_inter` from `stepA_cap_le`.  These are the concrete Step A caps consumed
by `net_multiplicity` at the base scale or a smaller nonnegative radius, and
by `NetLimitData.inter_count` at the item-5 ratio scale.  Verification passed
for the focused file check and the targeted `MetricCompactnessInputs` module;
the endpoint `metricCompactness` `sorry` remains unchanged.

Added checked bundle-level Step A adapters: `net_mult`, `inter_count`,
`exists_net_data`, `exists_stable_net`, and `exists_stepA_net`.  These route
the existing Step A net and multiplicity theorems through a single
`MetricCompactnessInputs` value, so the later D6 assembly can obtain the
stable `NetLimitData` plus the item-5 intersection count without rethreading
`decay`, `pack`, `volume`, `dist_eq`, and the cap projections by hand.
Verification passed for the focused file check and the targeted
`MetricCompactnessInputs` module; the endpoint `metricCompactness` `sorry`
remains unchanged.

Added checked D6-facing wrappers `subseq`, `properMetrics`, and `stepA_net`.
The bundle now reindexes all Step A and Step B honest inputs along a
subsequence, produces the per-member `ProperMetricOn` family from the
endpoint's `SeqMetricComplete` and connectedness hypotheses, and obtains the
Step A net package directly from endpoint hypotheses.  Verification passed
after refreshing the new Step B `.subseq` exports; the endpoint
`metricCompactness` `sorry` remains unchanged.

Refreshed the remaining endpoint hypothesis reindexing API:
`SeqMetricComplete.subseq` and `SeqBoundedGeometry.subseq` are now checked and
built in their native files.  D6 can use these wrappers after composing Step
A/D subsequences instead of manually reindexing completeness and curvature
derivative bounds.  The next concrete D6 input-threading target is a composed
subsequence adapter that combines the existing `MetricCompactnessInputs.subseq`
with these endpoint wrappers and the already checked `BaseInjBound.subseq`.

Added checked `stepA_net_subseq`, which applies the bundled Step A net package
after reindexing by a subsequence and reuses `SeqMetricComplete.subseq` for the
proper metric realization.  This completes the local D6 input-threading adapter
for Step A nets after diagonal subsequences.  A first product-shaped helper for
bundling `SeqMetricComplete`, `SeqBoundedGeometry`, and `BaseInjBound` failed
because ordinary `Prod` is the wrong wrapper for these `Prop` hypotheses; it
was removed in favor of the direct consumer theorem.

Verification passed.  The endpoint `metricCompactness` `sorry` remains
unchanged.

## 2026-07-10 uniform branch-radius audit

The bundled `normalBounds` field does not currently entail the uniform radius
used in older D6 plan prose.  Its constants are uniform, but
`NormalCoordMetricBoundInput.radius` has only pointwise positivity and may tend
to zero with the member index.  Consequently `Item3RadiusInput`,
`Item3GpScaleInput`, and a globally `k`-independent `SigmaScaleField` cannot be
discharged from the present bundle merely by choosing `D` large.

No endpoint assumption was added.  The honest next choice is either to produce
a sequence-uniform quantitative normal-coordinate inverse-exp radius from the
book's bounded-geometry hypotheses, or to redesign the B/C construction around
fixed-index local radii together with an explicit diagonal/eventual argument.
The conditional endpoint remains 0% proved.

## 2026-07-13 Gate 6 floor and fixed-`D` producer order

`NormalRadiusProfile` now derives the positive coefficient
`gpRatio = sqrt (1 / 2) * ratio`.  The checked theorems `floor_le_expGp` and
`mul_lambda_lt_expGp` give the real relative floor for `expRadiusGp`; they do
not confuse it with the older `expMapC2Radius` floor and add no endpoint field.

The fixed-`D` quantifier order is now explicit.  `MetricCompactBase` stores the
D-independent geometric data and a packing family
`forall D > 0, PackingBound D`.  `MetricCompactBase.exists_largeD` chooses one
real divisor satisfying `1 < D`, `mu 0 <= D`, an aggregate scalar budget
`c < gpRatio * D`, and the existing nonlinear `stepA_cap_le`.  The proof uses
the uniform exponential bound after `lambda D 0 <= 1`; no new mathematical
input is hidden.  `MetricCompactnessInputs.ofBase` and `exists_ofBase` then
instantiate packing only after that choice and return the original fixed-`D`
consumer bundle.  Existing consumers and subsequence APIs are unchanged.

The D-audit also found the remaining honest boundaries.  A direct
`4 * lambda` budget uses `c = 4`, while the current `lambda_window` loses a
factor two, so a finite-slot eventual `4 * lamInf` proof needs budget `c = 8`.
The present all-index `Item3GpScaleInput` is stronger than that eventual fact.
The full minimizing cage additionally depends on `A_D(r)` and the not-yet-fixed
center radius, both available only after packing at the selected D; it is not a
consequence of the generic profile budget alone.  Hessian/Neumann remains an
independent frontier.

Focused verification and the targeted refresh passed.  The Gate 6
floor/selection brick is complete; the selected minimizing-branch Gates 1--6
machinery is complete.  `StepB1RawInput` producer theorem and textbook B1 are
still 0%; dedicated Step-B/B1 machinery is about 79%, Chapter 4 machinery about
75%, and whole-HCG machinery about 52%.  Conditional and final compactness
endpoints remain 0%.

## 2026-07-13 post-packing Item 3 tail

`NormalRadiusProfile.gpScaleTail` now discharges the real construction
quantifiers after `D`, `pb`, and `r` have been selected. It takes the scalar
budget `8 < gpRatio * D`, intersects `lambda_window` over the finite range
`pb.A r`, identifies each live net radius through `ProperMetricOn.dist_eq`,
and concludes `Item3GpScaleTail`.

The factor eight is genuine: the lower window is
`lamInf / 2 <= lambda(seqRadius)`. No endpoint field was added, and the
strong legacy all-index `Item3GpScaleInput` was not fabricated from the
profile. Focused verification and the narrow producer/consumer refresh
passed. The legacy all-index `Item3RadiusInput` still had to be replaced by a
finite tail; `SigmaScaleField` and Hessian/Neumann remain independent.

The `g_p` post-packing quantifier sub-brick is 100%. The concrete
`StepB1RawInput` producer theorem and textbook B1 theorem remain 0%; dedicated
Step-B/B1 machinery is about 80%, Chapter 4 machinery about 76%, and whole-HCG
machinery about 53%. Conditional and final compactness endpoints remain 0%.

## 2026-07-13 finite item-3 radius and one-shot divisor

`NormalRadiusProfile.radiusScaleTail` now finite-intersects the lower half of
`lambda_window` and proves `Item3RadiusTail` from the two exact scalar budgets
`2 * a < D` and `2 * a < ratio * D`.  It obtains the strict injectivity-radius
bound from `mu_hasInj_of_le` and the `expMapC2Radius` bound from
`mul_lambda_lt_exp`.  The corresponding fixed-index exp-ball consumer is
checked in `GoodCoveringItem3.lean`.

For the book factor
`a_D = 205 * exp (C * (20 * lambda D 0))`, `MetricCompactBase.exists_item3D`
uses one aggregate call to `exists_largeD`.  The estimate
`2 * a_D <= 410 * exp (20 * C)` follows from `lambda D 0 <= 1`; the aggregate
constant simultaneously yields the `g_p`, injectivity, normal-radius, and Step
A cap budgets.  `exists_item3OfBase` instantiates packing only after this single
choice, and `item3ScaleTails` produces both finite tails from the resulting
fixed-`D` bundle.  Focused checks and targeted refreshes passed.

The exp-diffeomorphism radius sub-brick is 100%.  The full textbook item-3
geodesic-convexity theorem, concrete `StepB1RawInput` producer, textbook B1,
and compactness endpoints remain 0%.  Dedicated Step-B/B1 machinery is about
81%, Chapter 4 machinery about 77%, and whole-HCG machinery remains about 53%
after conservative rounding.  The next independent frontiers are the
sigma/`r₁` domain ledger, physical cage/radius assembly, and Hessian/Neumann.

## 2026-07-13 arbitrary extra budget for the physical cage

`MetricCompactBase.exists_item3D` now accepts an arbitrary real `c₀` before
choosing `D`.  The same one-shot selection returns
`c₀ < gpRatio * D`, the finite-tail budgets `8 < gpRatio * D` and
`16 < ratio * D`, the inverse-transition-domain inequality
`8 * lambda D 0 < r₁`, both factor-two item-3 radius inequalities, and the
nonlinear Step-A cap.  `exists_item3OfBase` preserves these outputs while
instantiating `PackingBound D` only after that single `D` has been chosen.

This arbitrary budget is the bridge to the already selected minimizing scale:
after `normalMinScale` supplies one positive `aMin`, choose
`c₀ = (8 * exp C / aMin) * gpRatio`.  The checked
`physScale_of_extra` cancels the positive `gpRatio` and converts the resulting
extra inequality into the exact slotwise cage budget
`8 * exp C < aMin * D`.  No parallel divisor selector, endpoint radius field,
or all-index radius assumption was introduced.

The one-shot divisor/`r₁`/physical-scale selector sub-brick is 100%.  The
selected minimizing-branch Gates 1--6 machinery is 100%, while the concrete
`StepB1RawInput` producer theorem, textbook B1 theorem, full item-3
geodesic-convexity theorem, and compactness endpoints remain 0%.  Dedicated
Step-B/B1 machinery is about 83%, Chapter 4 machinery about 79%, and whole-HCG
machinery remains about 53% after conservative rounding.  The remaining
high-level actual-transition/POU/`StrictDistInput` assembly and the
Hessian/Neumann argument are independent frontiers.

## 2026-07-13 half item-3 intrinsic-radius tail

`NormalRadiusProfile.halfGpScaleTail` now converts the existing item-3 budget
`2 * a < ratio * D` into the finite eventual estimate
`(a / 2) * lamInf gamma < expRadiusGp` at every selected live center.  The proof
uses the lower half of `lambda_window` and the already checked inequality
`1 / 2 < sqrt (1 / 2)`; it adds no new fixed-`D` field or endpoint radius
assumption.  Focused verification passed.  A targeted object refresh was
temporarily obstructed by concurrently rebuilding shared curvature objects;
the theorem itself is checked.

This closes the intrinsic target-radius scalar needed by stable-pair transition
containment.  The local tail producer is 100%; the selected Gates 1--6 machinery
remains 100%.  Dedicated Step-B/B1 machinery is about 83%, Chapter 4 machinery
about 79%, and whole-HCG machinery about 53%.  `StepB1RawInput`, textbook B1,
and the conditional compactness endpoint remain theorem-level 0%.

## 2026-07-13 H6 metric-radius tail

`NormalRadiusProfile.metricScaleTail` now proves that every selected finite
packing center eventually satisfies
`a * lamInf gamma <= normalBounds.radius`.  Its hypotheses are only positivity
of `D` and `a`, the existing budget `2 * a < ratio * D`, the proper-metric
realization, and the already selected net-limit/packing data; it does not use
the independent injectivity budget `2 * a < D`.

The proof transports the lower half of `lambda_window` to the selected center
through `ProperMetricOn.dist_eq`, then applies the original profile's
`le_radius` field.  No structure or compatibility wrapper was added.  Focused
verification passed.  This local metric-radius producer is 100%; the conservative
project estimates remain: selected Gates 1--6 machinery 100%, dedicated
Step-B/B1 machinery about 83%, Chapter 4 machinery about 79%, and whole-HCG
machinery about 53%.  `StepB1RawInput`, textbook B1, and both compactness
endpoints remain theorem-level 0%.

## 2026-07-13 removal of the endpoint S6 field

The H6 transition/atom route no longer consumes the sequence-level
`ExpInverseDerivBoundInput`, so the obsolete `expInvDeriv` field has been
removed from both `MetricCompactBase` and `MetricCompactnessInputs`.
`ofBase`, `ofUniformVolume`, and `subseq` now move only the surviving H6,
packing, volume, realization, and Step-A data.

The one-shot divisor selector no longer includes the auxiliary
`S = 8 * mu 0 / r₁` budget and no longer returns the old `hsigma` conjunct.
All genuine item-3 constraints remain: the requested aggregate `gpRatio`
budget, the constants `8` and `16`, both factor-two radius inequalities, and
the nonlinear Step-A cap.  A repository search found no remaining Lean caller
of the removed bundle field and no caller of the shortened
`ofUniformVolume` argument list.  Focused verification passed.

This supersedes the historical `r₁` claims in the earlier same-day selector
entries above.  Removal of S6 from the conditional endpoint bundle is 100%; it
does not prove a compactness theorem.  The selected Gates 1--6 machinery
remains 100%, dedicated Step-B/B1 machinery remains about 83%, Chapter 4
machinery about 79%, and whole-HCG machinery about 53%.  `StepB1RawInput`,
textbook B1, and the conditional and final compactness endpoints remain
theorem-level 0%.
