# StepCAveragePOU.lean

## 2026-06-30

Added the first bridge from the finite Step-C POU layer to the generic
center-average convergence API.

Implemented:

- `NetLimitData.hatSourceBall`, the fixed source ball for one frozen Step-C
  source index, using the realized proper metric from the good-covering layer;
- `NetLimitData.hatPOUDataTwo`, the two-index adapter for POU active data.
  The POU weights do not depend on the two convergence indices, but
  `centerAverage.unifTwoIdDataOn` expects an `a,b`-indexed data package.  This
  theorem reshapes `NetLimitData.hatPOU_active_data` into that consumer shape;
- `NetLimitData.unifHatIdOn`, the frozen-source POU averaging consumer.  It
  applies `centerAverage.unifTwoIdDataOn` with source set `hatSourceBall`,
  active regions `hatBall`, weights `rho`, and the two-index POU package from
  `hatPOUDataTwo`.

The attempted fuller frozen averaging theorem was deliberately not kept in this
pass.  The useful seam is now clear: the POU source ball is stated with the
`ProperMetricOn.ms` metric, while the center-average estimates use the
Hopf-Rinow/Riemannian metric for distances.  The generic averaging theorem can
take an arbitrary source set, so the next assembly layer should use
`hatSourceBall` as that set and separately provide the Riemannian completeness,
radius, active-map, and strict-convexity inputs.  `unifHatIdOn` now performs
exactly that routing.  It should not identify the proper-metric closed ball
with a Riemannian closed ball unless a later theorem explicitly uses the
proper-metric realization bridge.

Remaining boundary:

- instantiate the theorem with the concrete Step-B local maps;
- prove the active local-map convergence on each `hatBall`;
- provide the Riemannian radius and strict-convexity inputs on `hatSourceBall`.

Verification status: focused Lean check and targeted module build passed.  The
axiom probe for the new public declarations reports only the usual project
axioms.  No new `sorry` or `admit` occurs in this file.  The frozen-source POU
averaging consumer passed the same focused check, targeted build, and axiom
probe.

## 2026-06-30, compact-cage bridge

Added the next reusable assembly layer for feeding concrete Step-B local maps
into the frozen-source averaging consumer.

Implemented:

- `NetLimitData.hatSourceCompact`: the fixed source ball is compact in the
  stored manifold topology.  The proof uses the realized proper metric's closed
  ball compactness and converts the topology through `ProperMetricOn.top_eq`;
- `NetLimitData.hatBallInCompact`: every finite hat is contained in a compact
  closed-ball cage in the stored manifold topology.  If the net center is dead,
  the compact cage is empty; if it is alive, the open hat is contained in the
  matching closed `4 * lamInf` ball;
- `NetLimitData.hatPtsOfCompact`: compact-cage convergence on any chosen
  active compact superset supplies the exact active-region `hpts` input needed
  by `unifHatIdOn`.

The key design point is that compactness is stated in the manifold topology,
not only in the temporary proper-metric topology.  This avoids a later mismatch
when the center-average estimates install the Hopf--Rinow Riemannian metric for
the `dist` expression while the finite hats are still defined using the
realized proper metric.

Remaining boundary:

- instantiate `hatPtsOfCompact` from the actual Step-B transition/composition
  maps.  The currently missing concrete layer is the map/domain package that
  identifies, for each active hat, the Step-B Euclidean compact on which
  `comp_cInf_id_on` applies and then translates its order-zero estimate back to
  the manifold-valued `ptsSeq` used by the average;
- provide the Riemannian radius and strict-convexity inputs on `hatSourceBall`
  for that same concrete `ptsSeq`.

Verification status: focused Lean check and targeted module build passed.  The
axiom probe for the new compact-cage declarations reports only the usual
project axioms.  No new `sorry` or `admit` occurs in this file.

Post-audit of the next concrete step:

- `StepBApproxIso.comp_cInf_id_on` is available and is the correct Euclidean
  engine for the local composition maps;
- `StepBTransition` exposes fixed-pair `normalTransition` convergence data;
- there is not yet a concrete finite-hat map/domain package that, for each
  active `gamma`, chooses the relevant normal-coordinate domains, proves the
  active hat/source points lie in those domains or compact subsets, defines the
  manifold-valued `ptsSeq` consumed by `unifHatIdOn`, and translates the
  Euclidean order-zero `comp_cInf_id_on` estimate into the Hopf--Rinow
  manifold `dist` statement.

That missing map/domain package is the current Step C assembly frontier.  It
looks like a substantial interface brick, not a local proof-search issue in
`StepCAveragePOU.lean`.

## 2026-06-30, inverse-chart convergence bridge

Added the normal-coordinate bridge needed by the future concrete Step-B
finite-hat package:

- `chartSymmUnif`: on any compact coordinate set contained in a normal chart
  target, the inverse normal chart is uniformly continuous when the manifold
  side is measured by the Hopf--Rinow Riemannian metric;
- `chartSymmIdConv`: a two-index Euclidean convergence-to-identity estimate on
  such a compact coordinate set becomes the corresponding Hopf--Rinow
  manifold-distance estimate after applying the inverse normal chart;
- `chartPtsConv`: the source-point version needed for actual local maps.  If
  source points lie in the chart source, their chart coordinates lie in the
  compact coordinate set, and the two-index coordinate maps converge to the
  identity there, then the decoded points
  `(normalChartAt g p).symm (F a b ((normalChartAt g p) x))` converge to `x`
  in Hopf--Rinow manifold distance.

This removes the analytic/topological part of the coordinate-to-manifold
translation.  The remaining Step C frontier is narrower and unchanged in kind:
the project still needs the concrete finite-hat local-map/domain package that,
for each active hat, chooses the Step-B normal-coordinate compact, proves the
active source points and perturbed coordinates stay in it, and supplies the
Euclidean estimate from `StepBApproxIso.comp_cInf_id_on`.

Post-audit of the next consumer: the current Step-B transition theorem is still
fixed-pair data, while the Step-C files expose only abstract `ptsSeq`.  There
is not yet a finite-hat package choosing those chart centers/domains and
building the actual decoded `ptsSeq`, so `chartPtsConv` is the last generic
coordinate-to-manifold bridge before that package.

Verification status: the focused Lean check and targeted module build for
`StepCAveragePOU.lean` passed after adding these bridges.  The axiom probe for
the bridge declarations reports only the usual project axioms.  No new `sorry`
or `admit` occurs in this file.

## 2026-06-30, per-hat decoded-map hpts adapter

Added `NetLimitData.hatChartPts`.

This is the first finite-hat-shaped adapter after the generic chart bridge.  It
takes, for each hat `gamma`, an honest chart center, compact coordinate set,
two-index coordinate map, source/domain membership, compact-target membership,
compact-preservation, and Euclidean convergence-to-identity.  It returns the
exact active-region convergence shape consumed by `unifHatIdOn` for decoded
points
`(normalChartAt g center_gamma).symm (F_gamma a b ((normalChartAt g center_gamma) x))`.

This intentionally does not manufacture the missing Step-B data.  The remaining
frontier is now the concrete producer that chooses those centers/coordinate
compacts/maps from the Step-B transition and good-covering data, and proves the
membership/compact-preservation hypotheses.

Verification status: the focused Lean check and targeted module build passed
for this adapter.  Its axiom probe reports only the usual project axioms.  No
new `sorry` or `admit` occurs in this file.

## 2026-07-01, source-image compact cage adapters

Added `chartPtsSrcK`, `NetLimitData.hatChartPtsSrcK`, and
`NetLimitData.hatSrcPtsOfComp`.

`chartPtsSrcK` is the source-compact variant of `chartPtsConv`: if a compact
source cage lies in a normal chart source, its image under the normal chart is
the compact coordinate set used by the existing inverse-chart convergence
bridge.  This removes the need for downstream Step-B/Step-C assembly code to
manufacture a separate `coordK`, target-containment proof, and coordinate
membership proof when those data are just the chart image of a compact
manifold-side cage.

`hatChartPtsSrcK` lifts that adapter to the finite-hat shape.  For each active
hat it takes a compact source cage containing
`hatSourceBall ∩ hatBall_gamma`, a chart-source inclusion for that cage, and
Euclidean convergence/compact-preservation on the chart image.  It returns the
same active-region decoded-point convergence input consumed by `unifHatIdOn`.

`hatSrcPtsOfComp` is the source-cage version of `hatChartPtsOfComp`.  It applies
`comp_tendsto_id_on` with the compact set
`normalChartAt center_gamma '' sourceK_gamma`, so the finite-hat producer only
has to route Step-B domains over those image compacts instead of introducing a
separate coordinate compact family.

Remaining boundary:

- the concrete finite-hat producer still has to choose the source cages and
  Step-B transition maps from good-covering/Step-B data;
- radius, active-map, and strict-convexity inputs for the center average are
  still separate and unchanged.

Verification status: focused Lean check and targeted module build passed for
the new adapters.  Their axiom probe reports only the usual project axioms.
No new `sorry` or `admit` occurs in this file.

## 2026-07-01, source-cage decoded composition average wrapper

Added `NetLimitData.unifHatSrcOfComp`.

This is the full frozen-source averaging endpoint corresponding to
`unifHatIdOfComp`, but with source cages instead of a manually supplied
coordinate compact family.  It combines `hatSrcPtsOfComp` with `unifHatIdOn`.
The concrete finite-hat producer can now supply, per active hat, a compact
manifold-side cage containing `hatSourceBall ∩ hatBall_gamma`, prove that cage
lies in the appropriate normal-chart source, and route Step-B composition on
the chart image.

Remaining boundary:

- choose the actual source cages, Step-B domains, and transition maps from
  good-covering and Step-B transition data;
- provide the center-average radius, active-map, and strict-convexity inputs
  for the same decoded point family.

Verification status: focused Lean check and targeted module build passed for
the new wrapper.  Its axiom probe reports only the usual project axioms.  No
new `sorry` or `admit` occurs in this file.

## 2026-07-01, canonical source cage

Added `NetLimitData.hatSourceCage`, `hatCageData`, `hatCageCompact`, and
`hatCageSub`.

The canonical source cage for a finite hat is
`closure (hatSourceBall ∩ hatBall_gamma)`.  It is compact because
`hatSourceBall` is compact in the stored manifold topology and hence closed;
the closure of the active slice stays inside that compact source ball.  The
active slice is contained in the cage by `subset_closure`.

This removes two routine obligations from the future concrete finite-hat
producer: it can use `hatCageCompact` for `hKsrc` and `hatCageSub` for
`hSsub` when calling `unifHatSrcOfComp`.  The genuine geometric obligation is
unchanged and still visible: the producer must prove each canonical cage lies
in the relevant normal-chart source, and then route Step-B transition domains
and composition preservation over the chart image of that cage.

Verification status: focused Lean check and targeted module build passed.  The
axiom probe for the new declarations reports only the usual project axioms.
No new `sorry` or `admit` occurs in this file.

## 2026-07-01, live-center source-domain reduction

Added `NetLimitData.hatCageInClosed` and `NetLimitData.hatCageSrcOfBall`.

If a finite hat is live with center `c`, the canonical cage
`closure (hatSourceBall ∩ hatBall_gamma)` lies in the proper-metric closed ball
`closedBall c (4 * lamInf_gamma)`.  The proof converts closedness of that
proper-metric closed ball back to the stored manifold topology using
`ProperMetricOn.top_eq`, then applies `closure_minimal` to the active hat
containment.

`hatCageSrcOfBall` turns this into the exact normal-chart source inclusion
needed by the source-cage averaging wrapper: it is enough for the concrete
finite-hat producer to prove
`closedBall (center gamma) (4 * lamInf_gamma)` is contained in
`(normalChartAt metric (center gamma)).source`.

This narrows the next Step-C geometric producer.  Instead of proving
`hatSourceCage_gamma ⊆ normalChart.source` directly, the next layer should use
the Step-A radius/injectivity inputs to prove the closed `4 * lamInf` ball sits
inside the normal-coordinate source at the live net center.

Verification status: focused Lean check and targeted module build passed.  The
axiom probe for the new declarations reports only the usual project axioms.
No new `sorry` or `admit` occurs in this file.

## 2026-07-01, radius-only normal-source bridge

Added `properBallSrcOfRad`, `NetLimitData.hatCageSrcOfRad`, and
`NetLimitData.hatSrcPtsCageComp`.

`properBallSrcOfRad` uses the Gauss-lemma projection
`memNChartSrcOfDist`: if a realized proper-metric closed ball has radius
`R < expRadiusGp g c`, then it lies in `(normalChartAt g c).source`.  The
proof uses `ProperMetricOn.realizes` to identify the proper distance with the
stored Riemannian emetric and discharges the tangent-enorm formula locally.

`hatCageSrcOfRad` combines this with `hatCageInClosed`, so the finite-hat
source-domain obligation is now exactly
`4 * lamInf_gamma < expRadiusGp metric center_gamma`.  `hatSrcPtsCageComp`
specializes the decoded Step-B composition convergence wrapper to the canonical
`hatSourceCage`, internally discharging compactness, active-slice containment,
and source-domain membership from the live-center and radius inputs.

The remaining producer is a genuine radius-choice input: the current item-3
package gives an exponential diffeomorphism from a supplied coordinate radius
with `rho <= expMapC2Radius` and injectivity control, but it does not imply the
`4 * lamInf < expRadiusGp` inequality needed for the full canonical cage.  That
scale choice should be produced explicitly rather than hidden behind another
wrapper.

Verification status: focused Lean check and targeted module build passed.  The
axiom probe for the new declarations reports only the usual project axioms.
No new `sorry` or `admit` occurs in this file.

## 2026-07-01, source completeness projection

Added `NetLimitData.sourceComplete`.

This is a routine projection from `SeqMetricComplete X` to the exact
`CompleteSpace` local-instance spine required by the finite-hat averaging
theorems.  It uses `MetricComplete.complete` on the frozen source term
`X.obj (L.phi n)` and leaves the connectedness input separate because
connectedness is a different geometric hypothesis.

This does not change the remaining Step C frontier.  The finite-hat producer
still has to choose the actual Step-B domains, compact coordinate cages,
radius/strict-convexity facts, and active-map membership facts.

Verification status: the focused Lean check and targeted module build passed
for this projection.  Its axiom probe reports only the usual project axioms.
No new `sorry` or `admit` occurs in this file.

## 2026-07-01, decoded wrapper consumes sequence completeness

Updated `NetLimitData.unifHatIdOfComp` to take
`hX : SeqMetricComplete X` instead of an explicit local `CompleteSpace`
instance spine.  The theorem now instantiates that routine proof internally
using `NetLimitData.sourceComplete`.

This keeps `unifHatIdOn` generic but makes the Step-C decoded composition
wrapper match the sequence-level producer package.  The remaining finite-hat
frontier is unchanged: concrete Step-B domains, compact coordinate cages,
radius/strict-convexity facts, and active-map membership facts are still the
real missing data.

Verification status: the focused Lean check and targeted module build passed
for this interface cleanup.  Its axiom probe reports only the usual project
axioms.  No new `sorry` or `admit` occurs in this file.

## 2026-07-01, canonical-cage averaging wrapper

Added `NetLimitData.unifHatCageComp`.

This is the canonical-source-cage version of the frozen-source decoded
composition averaging endpoint.  It combines `unifHatSrcOfComp` with the
already proved canonical cage adapters, so downstream code no longer has to
provide a separate `sourceK`, compactness proof, active-slice containment
proof, or normal-chart source inclusion.  Those are discharged internally from
`hatSourceCage`, `hatCageCompact`, `hatCageSub`, and `hatCageSrcOfRad`.

The honest remaining inputs are exactly the still-real finite-hat producer
obligations: live centers, the radius inequality
`4 * lamInf_gamma < expRadiusGp metric center_gamma`, Step-B map/domain
preservation on the canonical cage chart image, the transition convergence and
limit identity data, and the center-average radius/active-map/strict-convexity
facts.

Verification status: the focused Lean check and targeted module build passed.
The first check attempt timed out and left a stale Lake lock plus an orphan
Lean worker; after the worker exited, the stale Lake lock was released and the
same focused check passed.  No new `sorry` or `admit` occurs in the edited
file.

## 2026-07-01, decoded composition average wrapper

Added `NetLimitData.decodedCompPts` and `NetLimitData.unifHatIdOfComp`.

`decodedCompPts` names the manifold-valued point family obtained by decoding
the two-sided Step-B coordinate composition
`A_gamma,b (B_gamma,a ((normalChartAt center_gamma) x))` through the inverse
normal chart at the hat center.  `unifHatIdOfComp` then combines
`hatChartPtsOfComp` with `unifHatIdOn`: once the concrete finite-hat layer
supplies the Step-B map/domain data and the routine radius, active-map, and
strict-convexity inputs, the POU center-average converges uniformly to the
identity on the frozen source ball.

This is still not the full finite-hat producer.  The remaining producer
frontier is now exactly the concrete choice of domains, compact coordinate
cages, radius/strict-convexity facts, and active-map membership facts for the
actual Step-B transition maps.

Verification status: the focused Lean check and targeted module build passed
for this wrapper.  Its axiom probe reports only the usual project axioms.  No
new `sorry` or `admit` occurs in this file.

## 2026-07-01, self-centered POU averaging wrapper

Added `NetLimitData.unifHatIdSelfOn`.

This is the source-centered version of `unifHatIdOn`: the comparison ball is
centered at the source point `x`, so downstream finite-hat producers no longer
need to supply a separate `pSeq` center family or prove the target-in-ball fact
for `pSeq`.  The remaining honest inputs are still the radius positivity,
active-map membership in the source-centered radius ball, strict-convexity, and
the per-hat point convergence.  It consumes the new generic
`centerAverage.unifTwoIdDataSelf`.

The decoded composition and canonical-cage wrappers still have their older
`pSeq`-centered variants.  The next small cleanup is to add self-centered
decoded/cage variants that call `unifHatIdSelfOn`, rather than duplicating the
generic averaging proof again.

Verification status: the focused Lean check and targeted module build passed.
No new `sorry` or `admit` occurs in this file.

## 2026-07-01, decoded self-centered composition wrapper

Added `NetLimitData.unifHatIdSelfComp`.

This is the decoded Step-B composition version of the self-centered averaging
endpoint.  It combines `unifHatIdSelfOn` with the existing
`hatChartPtsOfComp`, so the decoded composition endpoint no longer needs a
separate center sequence or target-in-ball proof.  The remaining inputs are the
real finite-hat data: radius positivity, active-map membership in the
source-centered radius ball, strict-convexity, coordinate compact/domain
routing, and the Step-B convergence/limit-identity package.

I inspected the source-cage and canonical-cage wrappers.  They route through
the same pattern, but adding both immediately would duplicate large theorem
statements.  The next mechanical pass should add `unifHatSrcSelfComp` and
`unifHatCageSelfComp` by copying the existing source/cage wrappers and replacing
the final call with `unifHatIdSelfComp`; no new geometry is expected there.

Verification status: focused Lean check and targeted module build passed.  No
new `sorry` or `admit` occurs in this file.

## 2026-07-01, source/canonical self-centered wrappers

Added `NetLimitData.unifHatSrcSelfComp` and
`NetLimitData.unifHatCageSelfComp`.

These finish the self-centered route through the existing source-cage and
canonical-cage layers.  The source wrapper calls `unifHatIdSelfOn` with the
existing `hatSrcPtsOfComp` point-convergence adapter.  The canonical wrapper
then specializes the source wrapper to `hatSourceCage`, discharging compactness,
active-slice containment, and normal-chart source membership from
`hatCageCompact`, `hatCageSub`, and `hatCageSrcOfRad`.

The averaging-route plumbing no longer requires a redundant `pSeq` center
family at any of the generic, POU, decoded-composition, source-cage, or
canonical-cage endpoints.  The remaining Step C producer frontier is now the
real finite-hat data: live centers, the `4 * lamInf < expRadiusGp` scale
choice, Step-B map/domain preservation on the canonical cage chart image, and
the source-centered active-map radius/strict-convexity facts.

Verification status: focused Lean check and targeted module build passed.  No
new `sorry` or `admit` occurs in this file.

## 2026-07-01, source/cage subsequence projections

Added `NetLimitData.hatSourceBall_subseq` and
`NetLimitData.hatSourceCage_subseq`.

These are the source-side companions to `hatBall_subseq`: after a later
master-subsequence refinement, the frozen source ball and canonical source cage
for `L.subseq hψ` at index `k` reduce to the original objects for `L` at index
`ψ k`.  The cage proof must keep `NetLimitData.subseq` opaque long enough for
the source-ball and hat-ball projection simp lemmas to fire, then close the
resulting reflexive closure equality.

Verification status: focused Lean check and targeted module refresh passed.

## 2026-07-01, Step-B composition hpts adapter

Added `NetLimitData.hatChartPtsOfComp`.

This is the direct consumer of `StepBApproxIso.comp_tendsto_id_on` for the
finite-hat point-convergence input.  For each hat it takes honest Step-B local
map data `B_k -> B_inf`, `A_l -> A_inf`, the limit identity
`A_inf (B_inf v) = v`, the compact-domain routing `coordK_gamma subset U_gamma`
and `B_inf(coordK_gamma) subset V_gamma`, and compact preservation for the
finite composed maps.  It then instantiates `hatChartPts` with
`F_gamma a b v = A_gamma b (B_gamma a v)`.

This deliberately keeps the producer boundary visible.  The remaining Step C
assembly frontier is still the finite-hat package that chooses the actual
`U_gamma`, `V_gamma`, `A`, `B`, compact coordinate cages, and active-domain
membership facts from the good-covering and Step-B transition data.

Verification status: the focused Lean check and targeted module build passed
for this adapter.  Its axiom probe reports only the usual project axioms.  No
new `sorry` or `admit` occurs in this file.

## 2026-07-09, explicit-weight canonical-cage endpoint

Added `NetLimitData.unifHatCageData` alongside the existing POU-backed
`unifHatCageSelfComp`.

The new theorem keeps the same canonical-cage geometry and two-sided Step-B
transition hypotheses, but consumes an explicit weight family `mu` through
`centerAverage.WeightDataOn`.  It passes `hmu.data` directly to
`centerAverage.unifTwoIdDataSelf`, while the existing `hatSrcPtsOfComp` chain
still supplies the per-hat decoded-map convergence.  The old POU endpoint was
left unchanged.

Scope limitation: this endpoint assumes every nonzero weight is active in the
existing radius-`4 * lamInf` `hatBall`.  The book's chart-bump numerators are
supported in the larger radius-`5 * lamInf` balls, so this theorem does not by
itself instantiate the book weights or close the Step-B1 producer.  A genuine
support-set adapter or a consumer generalized to the book support balls is
still required.

Verification status: the focused Lean check passed, with no new `sorry` or
`admit`.

Progress accounting: `unifHatCageData` itself is complete (100%).  The concrete
book-weight producer remains unstated/unproved (0%), and textbook Step B1
remains 0%; this is a consumer-side bridge within roughly 50% complete Step-B
machinery and roughly 59--60% complete Chapter-4 machinery.

## 2026-07-09, dead-slot-compatible cage endpoint

The finite bound `A(r)` is an upper bound, so a `Fin (A r)` slot may have
`seqCenter = none`.  Requiring a live center at every slot was therefore
strictly stronger than the good-cover construction.

Added `hatCageSrcCases`: a dead slot has an empty canonical cage, while a live
slot uses `hatCageSrcOfRad` at its actual center.  Added `unifHatCageSrc`, the
explicit-weight averaging endpoint whose geometric input is the exact condition
the proof consumes:

`hatSourceCage gamma ⊆ (normalChartAt metric (center gamma)).source`.

The prior all-live `unifHatCageData` remains unchanged as a compatibility
wrapper/endpoint.  Both new declarations passed focused verification.  This
closes the dead-slot consumer-interface obstruction; constructing the concrete
atom family and its sequence-level convergence remains producer work.

## 2026-07-09, realized radial-data adapters

Added `properBallNormal`, the data-retaining companion of
`properBallSrcOfRad`: a point in a realized proper-metric ball below
`expRadiusGp` has a normal vector whose `g_c`-length equals the realized
distance.  Added `properExpDist`, which reads the same equality for a radial
exponential point.  Both live in this norm-aligned layer so downstream atom
proofs do not reinstall incompatible tangent-fibre norm instances.

Focused verification and the targeted module build passed.  These adapters are
reusable geometry producers; they do not change the theorem-level progress by
themselves.

## 2026-07-13, finite-hat active radius

Added `NetLimitData.exists_hat_radius`, the thin finite-hat specialization of
`centerAverage.exists_active_radius`.  It accepts a general two-index point
family and uniform convergence on each canonical `hatBall`.  A nonzero POU
weight is sent into that ball by `hatPOUDataTwo`; the generic finite-family
producer then chooses one `radSeq` which is positive on `hatSourceBall`,
strictly contains every active point distance, and tends uniformly to zero on
the source ball as both indices grow.

No coordinate-composition maps or new radius assumptions occur in this
adapter.  The focused Lean check passed.

Accounting: `exists_hat_radius` and this finite-hat active-radius specialization
are complete (100%).  Supplying the concrete point-family convergence is a
separate producer obligation, while the physical cage and strict-convexity
consumers remain incomplete; no Chapter-4 endpoint theorem advanced (0%).

## 2026-07-13, dead-slot composition cages

Added `NetLimitData.hatPtsCasesComp`, the dead-slot-aware canonical-cage
specialization of `hatSrcPtsOfComp`.  It installs `hatCageCompact` and
`hatCageSub` directly, and uses `hatCageSrcCases` for chart-source membership.
Consequently a radial source bound is required only when the corresponding
`seqCenter` is live; an empty/dead slot no longer carries a fictitious center
hypothesis.

The composition convergence, cage preservation, and compact-image hypotheses
remain the same as in the existing all-live `hatSrcPtsCageComp` wrapper.  The
focused Lean check passed.

Accounting: `hatPtsCasesComp` and the dead-slot consumer specialization are
complete (100%).  Concrete live-center radius and composition-map producers
remain downstream, and no Chapter-4 endpoint theorem advanced (0%).

Together, `exists_hat_radius` and `hatPtsCasesComp` close the finite-hat
specialization on the consumer side without reinstating an all-slots-live
assumption.  They do not construct the concrete arbitrary partner (`y`)
point-family, nor do they discharge `StrictDistInput`.  The latter remains the
independent Hessian/Neumann strict-convexity frontier; no compactness endpoint
is stated or proved here (0%).

## 2026-07-13, support-local decoded composition

`hatSuppPtsOfComp` and `unifHatSuppData` are focused-green. They run decoded
composition convergence only on nonzero-weight entries and use
`centerAverage.activeFill` at the averaging boundary. The new endpoint asks
only for `WeightDataOn ... Set.univ`; actual support containment is carried by
the separate `hSupp` hypothesis, so normalization no longer duplicates a
geometric hat-support assertion.

`hatSuppCageData` is also focused-green. For each slot it closes the actual
nonzero-weight support inside a caller-supplied compact source-local cage and
extends the closed limit-target condition to that closure. It does not assume
that the whole canonical cage maps into the reverse convergence domain, and it
does not assume that the full global source ball lies in every local normal
chart.

This completes the reusable support-local consumer and cage sub-brick (100%).
The remaining capstone work is the outer finite source-chart assembly: pull the
limit weights back on the appropriate local cages, totalize sparse pair maps
only across zero-weight slots, and replace the whole-`hatBall` point premise of
`exists_hat_cm_tail` by its support-local analogue. Pair-to-capstone integration
is about 78%; `StepB1RawInput`, textbook B1, and compactness endpoints remain
theorem-level 0%. Whole-HCG machinery remains about 53%.

## 2026-07-13, source-local generic support indices

`hatSuppCageData` and `hatSuppPtsOfComp` now expose their proof-generic shape:
the support index is an arbitrary type and the source set is an inferred
implicit parameter. Existing finite-hat callers continue to infer the old
`Fin` index and `hatSourceBall`; the sparse producer instantiates the same API
with the original dependent `InterSlot L ... alpha` and the single source patch
owned by `alpha`.

The proofs themselves did not use finite enumeration or the distinguished
whole source ball, so no mathematics changed. The generalized file is
focused-green with no local warning. This closes the support-index/API part of
the B/C architecture (100%); it does not close the independent
Hessian/Neumann `StrictDistInput` frontier or any compactness endpoint (0%).

## 2026-07-18, framed support-cage interface

The canonical source-cage path now uses the per-center orthonormal normal
coordinates. `properBallSrcOfRad`, `hatCageSrcOfBall`, `hatCageSrcOfRad`, and
`hatCageSrcCases` return source membership for `framedChartAt`. The generic
support closure theorem `hatSuppCageData` likewise takes and returns framed
chart sources and framed chart images, so its Step-C caller no longer has to
translate a raw chart image into the canonical H6 coordinates.

The older generic coordinate-convergence lemmas in this file were not
mechanically rewritten: they remain valid raw-coordinate utilities and are not
part of this canonical support seam. The framed support-cage declarations and
the whole file pass focused verification. No new hypothesis or parallel API
was added.

The framed support-cage seam is complete (100%). The live framed B/C raw-input
producer and textbook Step B1 theorem remain theorem-level 0% until the rest of
the downstream migration and revalidation are complete; whole-HCG support
machinery remains about 60%.

The selected support-local decoded-point path is now framed as well.
`chartPtsSrcK` was generalized to an explicitly selected partial chart, so its
compact-image and inverse-uniform-continuity proof is independent of either
normal-coordinate implementation. `hatSuppPtsOfComp` instantiates that helper
with `framedChartAt`, and `unifHatSuppData` now uses the same framed chart for
its source hypotheses, image hypotheses, active point family, and averaging
readout. This avoids any raw/framed equality wrapper.

The adjacent legacy whole-cage consumers still use their original raw decoded
point family; they were deliberately not swept by this selected-route repair.
Focused verification of the complete file passed. The selected framed
support-point sub-brick is complete (100%); the live `StepB1RawInput` producer
and textbook Step B1 remain theorem-level 0%, while whole-HCG support machinery
remains about 60%.
