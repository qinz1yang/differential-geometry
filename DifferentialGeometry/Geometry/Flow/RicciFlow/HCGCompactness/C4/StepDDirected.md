# StepDDirected.lean — D1b: the lbl406 directed system

## State (2026-07-13 alignment)

Focused `StepDDirected.lean` verification passes with no local `sorry` warning.
The `directed_of_b1` recursion body is now locally closed in this file:
the separated scalar gates (`sepTail`, `sepBeta`, `sepFeed_le_beta`,
`sepNextC0_le`, `sepNextCov_le`), exact-zero base (`reflSepData`), and
two-ledger `hacc` replacement all check.  The successor step uses the planned
split: peel-last forward via `compSepFwd`, peel-first reverse via `compSepRev`,
then fold equality/germ transport plus `BookApproxIsoSep.ofParts`, finally
restricting closed-ball data back to the required open-ball carrier.

Important caveat: this is not completion of the whole D1/B/C stack.
`compSepFwd` and `compSepRev` are now proved in `PullbackField.lean`, so the
separated-composition blocker is closed.  The F4/F5 uniform producer chain is
also now proved and verified through this file.  The false P-only `stepB1_approxIso`
was removed; `directed_of_b1` now takes an explicit `StepB1RawInput`.  Producing
that package from the conditional compactness inputs is still the B/C frontier.  The old single-`a` commented
scaffolds were removed from `StepDDirected.lean` so future `sorry` greps are not
misled by stale examples.

Progress accounting: the conditional D1b consumer body is 100% checked, while
the textbook D1b theorem from the endpoint hypotheses is 0%.  The missing producer
is `StepB1RawInput`, not F4/F5, F2, or the separated-composition organs.  Step-D
consumer machinery is 100%, and the conditional assembly `compactness_of_b1`
is 100% proved from that package.  The working `metricCompactness` endpoint
remains 0% because its body still waits on the concrete B/C producer.

Downstream check after refreshing `PullbackField.lean` passed: the proved
`compSepFwd`/`compSepRev` bodies do not break the D1b consumer.

The aligned tree also promotes `speed_le_of_c0` and `data_image_ball` to
`Distances.lean`; this file now consumes that public F2 API.  Downstream and
full alignment verification passed.

Next target outside this phase: produce `StepB1RawInput` from the honest C-track
data.  There is no independent Step D/F target unless that producer exposes an
actual interface mismatch.
The former F4 scaling gate is closed by `metricComp_mul`, explicit Claim-1/F3
constants, and the completed `lemma45_corII_unif`.

## State (2026-07-07)

GREEN (3954-job targeted build; C4 is NOT in the root import tree — bare `lake build` is
vacuous for C4, always use targeted builds):
- `speed_le_of_c0` — fiberwise speed bound from the c0 tensor error (CS at a g-ON basis).
- `data_image_ball` — lbl367 in recursion form: data on the closed r₂-eball maps
  eball(O,r) into closedEBall(ΦO, √(1+ε)r).  PROVED sorry-free.
- `PartialDiffeomorph.refl`, `chainComp` (the book's Ψ_{j,l}; Nat.rec with explicit motive).
- `exists_directedApprox` — the lbl406 endpoint, STATED with one precise sorry (the
  recursion body; consumes the sorry-backed `stepB1_approxIso` per the gate policy).

## Key conventions / traps (details in STEPD_PLAN codas 44–48)

- File is InnerProductSpace-ONLY (no explicit NormedSpace variable) — else `trans` from
  PullbackField freezes on the baked-spine mismatch.
- TangentNormDiamond suppress-attribute BEFORE the docstring of `data_image_ball`.
- enorm hypotheses are consumed as CALC legs, not rw (instances print identically but
  rw rejects).
- `pathELength_mono` needs explicit (γ:=)(a':=)(b':=).

## Next

The recursion proof: obtain `comp_cov_le_unif p` once; Nat.rec σ over B1 thresholds with
radii 2^j and tolerances (C_j⁻¹2⁻ʲ per the book, C_j from the uniform constant); composite
data by l-induction over the C-parameterized `partialData_comp` + `.mono` +
`data_image_ball` for the K₂-nesting; j₀ := max(1 − log₂ ε, p).

## Dependent-Nat-cast lesson (chainComp'_snoc / chainComp_coe_head)
For `l→l+1` telescoping where the target index appears as `(j+1)+l` on one side and `j+(l+1)` on
the other (propositionally equal, NOT defeq — `Nat.add` recurses on the 2nd arg, so `(j+l)+1` is
the rfl-unfold but `(j+1)+l` is not), THREE naive tactics FAIL identically:
- `congr` on the dependent `Ψ`/`chainComp'` application → stuck HEq goals;
- `generalize (j+1)+l = k` → "result is not type correct" (the `▸`-cast PROOF depends on the index);
- `subst` → "not of the form x = t" (both sides are compound expressions, no variable).

WINNING route (all inside `chainComp'_snoc` succ):
1. free-target parameter on the `_snoc` statement so the IH matches any peeled index via its proof;
2. `subst h` at the top of each case to collapse the outer target cast to rfl;
3. eqRec-naturality helper
   `hcast : ∀ a (ha : (j+1)+l = a), Ψ_a (chainComp' … a ha y) = ha ▸ (Ψ_{(j+1)+l} (chainComp' … rfl y))`
   proved by `subst ha` (there the index IS a genuine variable);
4. `rw [hcast (j+(l+1)) (by omega)]` folds BOTH sides onto one shared base value under casts;
5. `simp only [eqRec_eq_cast]` closes the residual `castₗ v = castᵣ (castₘ v)` by proof irrelevance.

## Next: the `exists_directedApprox` recursion body
Forward ledger on `chainComp` (peel-tail; `partialData_comp` puts the accumulated error in slot 1,
coeff 1 up to the `1/(1−ε)` c0 correction).  Reverse ledger via `chainComp_coe_head` (express the
peel-tail composite as a peel-head bracketing onto `chainComp'`, so the accumulated tail is again in
the coeff-1 slot).  Budget: `e_l ≤ 2C·Σ_{i≤l} δ_i` on the geometric chain `δ_i = C⁻¹2⁻ⁱ` (book
lbl372).  Consumes B1's `stepB1_approxIso` threshold (sorry-backed per the gate policy — the
endpoint's axiom report will show B1's `sorryAx` until the B-track closes).

## 2026-07-07 (cont.): endpoint analytic + combinatorial cores proved
- `geomTailBudget` (sorry-free): `∀ ε>0 ∃ j₀ ∀ j≥j₀ ∀ l, ∑_{i∈range(l+1)} (1/2)^{j+i} ≤ ε`.
  The two-sided ledger's tail closes because C_p is absorbed into j₀ (per-step ε = plain 2⁻ⁿ).
- `exists_strictMono_ge` (sorry-free): `∀ T, ∃ σ StrictMono, ∀ j, T j ≤ σ j` (σ j = j + sup T).
Endpoint `exists_directedApprox` still one sorry = the accumulation with ball-radius bookkeeping
(`partialData_comp` l-induction + `compEpsAccum` + `geomTailBudget` + `data_image_ball`).

## 2026-07-07 (cont.): endpoint PRODUCER built
`exists_directedApprox` now has σ + Ψ + basepoint-preservation in place (green):
- T j = stepB1 threshold at (2^{j+1}, (1/2)^{j+1}, j); σ = exists_strictMono_ge T; Ψ = choose from
  stepB1 at (σj, σ(j+1)); basepoint from stepB1's 2nd conjunct.
- Gotcha: the goal's `letI` pack is not ambient — re-declare the 6 `letI : ∀ j, …` after refine.
The SINGLE remaining sorry = the per-composite accumulation (data bound): l-induction, base = refl
data, step via `partialData_comp` (re-extract stepB1's 3rd `Nonempty data` conjunct the producer
dropped) + `data_image_ball` radius propagation + `compEpsAccum`/`geomTailBudget` budget + reverse
via `chainComp_coe_head`.  Genuine multi-session ball-bookkeeping frontier.

## 2026-07-07 (cont.): base case PROVED + wired — endpoint = inductive step only
- `tensor02CovDeriv_metric_zero` (sorry-free, axiom-clean): `∇^{a+1}_g g = 0` in the C4 indexing
  (tensor02_eq_covDOF + covDerivOfField_eq_iterCov + iterCov_metric_zero + domDomCongr_zero).
- `reflBookData` (sorry-free, axiom-clean): identity `BookApproxIsoPartialData` for any ball/ε/p.
  Fiber-algebra: `MetricFiberData.inner D v w = D.flat v w` (LinearEquiv) ⟹ `inner0S _ 0 0 = 0`
  via `D.flat.map_zero`+`LinearMap.zero_apply` (bare `map_zero` mis-fires); `sub_self _` explicit.
- Endpoint data-bound now: intro ε p, j₀ from geomTailBudget, `induction l`: base l=0 closed by
  `reflBookData` (`chainComp Ψ j 0 = refl`), **step l+1 = the SINGLE remaining sorry**.
REMAINING = inductive step: `partialData_comp` (accumulated in slot 1) + `data_image_ball` radius
bookkeeping + budget + `chainComp_coe_head` reverse, re-extract stepB1 per-step data. Large frontier.

## 2026-07-07 (cont.): endpoint inductive-step frontier — 3 route findings
The endpoint's single remaining sorry (inductive step) has TWO distinct structural blockers found
by analysis, plus the geometric bookkeeping:
- **Route #2 (tolerance):** `partialData_comp` STRICTLY increases tolerance (ε''≥ε/(1−ε)>ε), so a
  fixed-ε induction can't close. Fix = accumulated tolerance `a_l`, `a_l≤ε` via `geomTailBudget`,
  final `BookApproxIsoPartialData.mono` (exists, PullbackField:1577) down to ε.
- **Route #3 (domain):** `partialData_comp` needs an `Opens` domain `U₁`, but the ball data is on
  `closedBall` (closed). Fix = restructure the accumulation onto OPEN balls with radius margins
  (`closedBall(2^j) ⊆ ball(r)`), √(1+ε)-growth via `data_image_ball`.
- Plus: re-extract stepB1's per-step `Nonempty data` (producer dropped it), F5 `hC` from
  `comp_cov_le_unif` (available), reverse ledger via `chainComp_coe_head`.
This is a genuine multi-session construction (the heart of D1b), now precisely characterized.

## 2026-07-08: correct open-ball shell BUILT (green) — step isolated with all inputs
`exists_directedApprox` now re-founded on the SOUND structure (was unsound fixed-ε):
- Producer keeps full per-step data: `choose Ψ hΨsrc hΨbase hΨdata using hΨex`.
- Member instances: RiemannianBundle / IsRiemannianManifold (member_isRiemannian) / ProperSpace (P.proper).
- Data-bound = `suffices ∀ l, ∃ a, 0<a ∧ a≤ε ∧ a≤1/2 ∧ Nonempty (Book (ball(2^j(1+2^{-(l+1)}))) a p …)`,
  finished per-l by `BookApproxIsoPartialData.mono` to (closedBall(2^j), ε). Base l=0 via reflBookData.
- ONE sorry = the l+1 composition step (all inputs present).
Blocker (classification): open-ball/radius bookkeeping (himg via data_image_ball + dist↔edist bridge
`P.realizes` + nested margins R_l>r₂>R_{l+1}>2^j) intertwined with tolerance-budget algebra (a_{l+1}
per partialData_comp's two bounds, ≤min(ε,1/2) via Cp-scaled geomTailBudget). Data-extraction DONE;
reverse ledger subsumed by two-sided partialData_comp. ~200-line multi-session construction.
Full `lake build` externally blocked by another agent's broken WIP in Tensor0SRiemannian/Comparison.lean.

## 2026-07-08: ball/eball radius bridges added

Added the two set-level metric/emetric radius bridges needed by the open-ball
accumulation shell:

- `ball_subset_eball_ofReal`: converts an open `Metric.ball` into the
  corresponding `Metric.eball` with `ENNReal.ofReal` radius.
- `closedEBall_ofReal_subset_ball`: converts a closed `Metric.closedEBall`
  with `ENNReal.ofReal` radius into a strictly larger open `Metric.ball`.
- `data_image_metric_ball`: composes the two bridges with `data_image_ball`,
  giving the direct `Metric.ball -> Metric.ball` image inclusion needed by the
  open-ball accumulation step.
- `two_pow_lt_openRad`: records that the open accumulation radius
  `2^j * (1 + (1/2)^(l+1))` strictly contains the closed `2^j` radius.

These are local bookkeeping helpers for the remaining `l+1` inductive step;
they do not close the Step D1b endpoint sorry.  Also removed the stale duplicate
`ExpInverseDerivBoundInput.subseq` from `StepCTransitionRefine.lean`, since the
canonical definition now lives in `StepBInputs.lean` and the duplicate caused an
import collision.

Verification: focused checks passed for `StepCTransitionRefine.lean` and
`StepDDirected.lean`.  Targeted refreshes passed for the stale/missing upstream
modules `StepCTransitionRefine`, `StepCAveraging`, `AllTimesBounds`,
`Evolution.Connection`, `MetricCovDerivPullback`, and
`Evolution.BernsteinShiHigher`.  A targeted
`StepDDirected` module refresh was attempted twice but timed out while replaying
wide dependencies; no Lean error from `StepDDirected.lean` was reported before
the timeout.

## 2026-07-08: D1b image inclusion and `partialData_comp` domain package green

Added the checked bookkeeping needed to feed the accumulated composite into the
next step:

- `chainComp_base`: every `chainComp` preserves basepoints when each step does.
- `openRad_succ_lt`, `midRad`, `openRad_next_lt_mid`, `midRad_lt_openRad`:
  the three radii now have the formal order `R_l > r2 > R_{l+1}`.
- `imageRad_lt_step` and `imageMid_lt_step`: the accumulated image radius,
  after the `sqrt (1+a)` growth, still fits inside the next book radius.

Inside the remaining `exists_directedApprox` `succ` branch, Lean now checks:

- accumulated data restricts from `ball(R_l)` to closed emetric balls at
  `R_{l+1}` and at `r2`;
- `data_image_ball`/`data_image_metric_ball` prove the centered image inclusion
  for both `ball(R_{l+1})` and `ball(r2)`;
- `U1 = ball(r2)`, `K2 = ball(2^(j+l+1))`, and
  `K = closedBall(R_{l+1})` are packaged for `partialData_comp`;
- `partialData_comp` instantiates successfully with the restricted D1/D2 data.

Verification: focused `StepDDirected.lean` check passed.  The endpoint still has
the same single `sorry`.

Remaining blocker: the current induction invariant only records
`0 < a`, `a <= ε`, and `a <= 1/2`.  The instantiated `partialData_comp` family
requires a new tolerance `ε''` above both
`a/(1-a) + δ * max C 2` and `δ/(1-δ) + a * max C 2`, while the next invariant
must keep `ε'' <= ε` and `ε'' <= 1/2`.  The next code change should strengthen
`hacc` with the quantitative geometric-ledger bound from `geomTailBudget`
rather than trying to derive that bound from `a <= ε` alone.

## 2026-07-08: ledger invariant strengthened and two-bracket entry exposed

The live `hacc` invariant now carries the uniform constant `B = max C 2`
outside the induction and records a quantitative geometric budget
`a_l <= 2 * B * sum_{i<=l} (1/2)^(j+i+1)`.  The `j0` threshold now comes from
`geomTailBudget (ε / (2 * B))`, not just `geomTailBudget ε`.

The invariant also carries both bracketings:

- left fold: data for `chainComp Ψ j l`;
- equality-parameter right fold: data for `chainComp' Ψ l j (j+l) rfl`.

Added two small transport helpers:

- `PreApproxIsoDataOn.congr_eq`: specialize the existing germ-congruence
  transport to globally equal maps.
- `BookApproxIsoPartialData.ofParts`: assemble partial book data from separately
  transported forward and reverse fields.

Added `chainComp_eq_right`, exposing the left/right fold equality that was
previously only a local lemma inside `chainComp_coe_head`.

Verification: focused `StepDDirected.lean` check passed.  The endpoint still has
the same single `sorry`.

Next target: use `chainComp_eq_right` plus `PreApproxIsoDataOn.congr_eq` to
transport the reverse field from the right-fold ledger, combine it with the
forward field from the left-fold ledger via `BookApproxIsoPartialData.ofParts`,
and then do the remaining scalar inequalities for the next `a_{l+1}`.

## 2026-07-08: reverse transport and next-tolerance wiring green

Added `symm_eventuallyEq_on_image`: if two partial diffeomorphisms agree on an
open source zone, their inverse maps agree as germs on the image of that zone.
In the `exists_directedApprox` succ branch this now proves the needed germ
equality between the right-fold inverse and the left-fold inverse over the
left-fold image of `U1`.

The succ branch now checks:

- `Dright_mid`: right-fold data restricted to the midpoint open zone;
- `hrev_germ`: inverse-germ equality on the relevant image open set;
- `Drev_left`: right-fold reverse data transported to the left-fold reverse map;
- `D1parts`: left-fold forward data plus transported reverse data reassembled
  via `BookApproxIsoPartialData.ofParts`;
- `partialData_comp` consumes `D1parts` and the step data.

Added `nextTol` with `nextTol_left`, `nextTol_right`, and `nextTol_pos`.  The
succ branch now defines `aNext = nextTol a δ B` and checks the two lower-bound
hypotheses needed by `partialData_comp`.

Verification: focused `StepDDirected.lean` check passed.  The endpoint still has
the same single `sorry`.

Remaining scalar obligation: prove `aNext < 1` and the strengthened budget
bound for `aNext`.  This is now isolated from the geometric, source, image, and
reverse-transport bookkeeping.

## 2026-07-08: scalar target audit corrected the next step

The previous "remaining scalar obligation" target is not the right next target
as stated.  The live succ branch calls the full two-sided `partialData_comp`
after transporting right-fold reverse data back onto the left-fold composite.
That full call requires the reverse-side lower bound
`δ / (1 - δ) + a * B <= ε''`, so the accumulated tolerance `a` is multiplied by
the fixed constant `B = max C 2` at each peel-last step.  This repeats the old
linear-budget failure recorded in the Step D plan: the current invariant
`a <= 2 * B * sum ...` cannot close this recurrence by scalar arithmetic alone.

Route audit:

- Directly proving the existing `aNext < 1` plus budget target would require a
  false linear recurrence; this is a route-choice failure, not a missing
  `nlinarith`.
- Choosing a larger `ε''` while still using full `partialData_comp` does not
  fix the endpoint, because the endpoint needs a tolerance still bounded by the
  geometric tail.
- The viable next route is to split the composition consumer along the book's
  two-bracketing design: use a forward-only composition producer for the
  peel-last `chainComp` ledger and a reverse-only composition producer for the
  peel-first `chainComp'` ledger, then assemble the two halves with
  `BookApproxIsoPartialData.ofParts`.

Verification: no Lean code was changed in this audit pass; the last focused
`StepDDirected.lean` check remains the current verification point.  The endpoint
still has the same single `sorry`.

Follow-up implementation note: `PullbackField.lean` now exposes the required
half-composition API as `compDataFwd` and `compDataRev` (checked signatures,
both currently precise `sorry` frontiers).  The next `StepDDirected` edit should
replace the live full `partialData_comp` call in the succ branch with:

- `compDataFwd` on `(chainComp Ψ j l).trans (Ψ (j+l))`, producing the forward
  data under the good bound `a/(1-a) + δ * B`;
- `compDataRev` on the peel-first bracketing for `chainComp'`, producing the
  reverse data under the good bound `a/(1-a) + δ * B` after swapping the
  accumulated/new slots;
- `BookApproxIsoPartialData.ofParts` plus the existing fold-equality/germ
  transport to assemble the final two-sided data.

Second follow-up audit: consuming `compDataRev` on the genuine peel-first
bracketing needs accumulated data for the shifted tail
`chainComp' Ψ l (j+1) (j+(l+1))`, while the current `hacc` induction only gives
data at the fixed start `j`.  The existing `chainComp'_snoc` tail-peel lemma is
not enough for the reverse budget: tail-peeling lets the current IH compose, but
then the reverse half again puts the accumulated tolerance in the `* B` slot.

Therefore the next `StepDDirected` code change must strengthen the recursion
invariant to be start-indexed (or otherwise supply the shifted-tail ledger):
for every allowed start `s >= j`, carry the same accumulated tolerance and
open-ball data for both `chainComp Ψ s l` and `chainComp' Ψ l s (s+l)`.  The
fixed-start invariant is too weak for the book's peel-first reverse estimate.

## 2026-07-09: hacc restart count, half-composition structure green

New `/goal` count restarted from 0.  Route error #1/3: the first start-indexed
`hacc` right-fold ledger was still target-fixed at `s + l`.  This is too weak
for the shifted-tail reverse step, because `ih (s+1)` naturally needs target
`s + (l+1)`, not the defeq shape `(s+1)+l`.  The invariant was strengthened to
carry the right-fold data in free-target form:
`∀ m, s + l = m -> BookApproxIsoPartialData ... (chainComp' Ψ l s m _)`.

Verified structural progress in `exists_directedApprox`: the `l=0` start-indexed
base case checks; the succ branch now consumes both shifted IH inputs, restores
the real `C = (comp_cov_le_unif p).choose` / `B = max C 2`, builds the forward
peel-last inputs, proves the midpoint image containment, calls `compDataFwd`,
builds the reverse peel-first inputs, proves the first-step image containment,
calls `compDataRev`, and assembles both right-fold and left-fold closed-ball
book data from the two halves.  Focused verification passed after these
structural changes; the endpoint still has the same `exists_directedApprox`
succ-branch `sorry`.

Route error #2/3: after the half-composition split, the remaining scalar ledger
is still not closed by the current linear budget
`a <= 2 * B * geometric_tail`.  The lower-bound recurrence still contains
`a/(1-a)`, so the proof cannot soundly derive the next budget from this linear
upper bound alone.  The next route should replace the linear-only hacc budget
with a recursive tolerance ledger (plus a separate proof that the recursive
ledger stays below `ε` and `1/2` for sufficiently late starts), then use the
already-checked structural half-composition assembly.

## 2026-07-09: route error 3/3, ordinary recursive ledger is still wrong

Route error #3/3 for the restarted `/goal`: a plain forward recursive tolerance
ledger is not enough either.  The obstruction is scalar, not geometry: the
half-composition lower bound still contains `a/(1-a)`.  Even with no new
per-step error, iterating `a ↦ a/(1-a)` sends `1/a` to `1/a - n`; any fixed
positive base tolerance from `reflBookData` eventually blows up as the composite
length `l` grows.  Therefore a usual `l`-induction with one forward-recursive
ledger cannot prove the required uniform-in-`l` endpoint.

Do not redo the already checked structure: start-indexed open domains,
free-target right-fold data, `compDataFwd`, `compDataRev`, and both closed-ball
assemblies are green.  The next viable design must either:

- use a target-length-indexed/backward tolerance allocation, so the identity
  base tolerance can be chosen depending on the final composite length; or
- strengthen/replace the half-composition scalar API so the accumulated term is
  additive/multiplicative in a book-compatible ledger rather than
  `a/(1-a)` at every recursive peel.

Verification status after recording this: focused `StepDDirected.lean` check
should still pass with the single endpoint `sorry`.

## 2026-07-09: hacc recount, first two new route errors

New `/goal` count restarted again from 0 after the previous 3/3 stop.

Route error #1/3: target-length/backward allocation does not repair the current
single-epsilon `BookApproxIsoPartialData` recurrence.  The obstruction is still
the same scalar transform in the public half-composition interface: once a
positive accumulated book tolerance enters a peel, the next lower bound contains
`a/(1-a)`.  Choosing the identity tolerance based on the final length only moves
where the first positive `a` is chosen; it does not give a uniform `forall l`
ledger under the current carrier.

Route error #2/3: strengthening the half-composition scalar API while keeping
the existing book-compatible partial-data carrier is not a local patch.  Live API
audit found that `PreApproxIsoDataOn` and `BookApproxIsoPartialData` carry one
`eps` for both `c0_small` and `cov_deriv_small`.  The only separated
metric-equivalence field is in the same-domain `IsApproxIsometryOn`, not in the
partial-map composition carrier.  In `PullbackField.lean`, `compDataFwd` already
requires `eps/(1-eps) + eps' * max C 2 <= eps''`, and `compDataRev` has the
mirror bound.  The `eps/(1-eps)` term is forced by converting the `c0_small`
metric-tensor error into the `MetricUniformEquivalentOn` parameter used by F5.

Next target for this recount: test whether a narrow separated-parameter producer
can be added below `BookApproxIsoPartialData` without changing the public book
endpoint.  If that also requires a new carrier/design decision rather than a
small reusable lemma, count it as route error #3 and stop with that API frontier.

Route error #3/3: the separated-parameter producer route is a real API/design
frontier, not a small local lemma.  F5's `eps0` must dominate three inputs at
once: the metric-equivalence parameter obtained from `c0_small`, the old
higher-order error towers, and the metric-tower input used for the background
metric.  A sound ledger therefore needs at least separate accumulated
parameters for `c0` and covariant-derivative error, with an F5 feed like
`max cov (c0/(1-c0))`.  The existing `PreApproxIsoDataOn` cannot express this,
because both `c0_small` and `cov_deriv_small` are stored under the same `eps`;
`BookApproxIsoPartialData` merely packages two such single-epsilon records.

Smallest remaining frontier: introduce a deliberate partial-map separated
carrier, or equivalently a pair of forward/reverse composition producers whose
statements carry distinct `c0` and cov parameters and wrap back to
`BookApproxIsoPartialData` only when both are below the final book tolerance.
This is expected to reuse most of `partialData_comp`'s proof organs, but it is
not safe to hide it as an arithmetic patch inside `exists_directedApprox`.

## 2026-07-09: separated API landed, hacc recount route errors

New `/goal` count restarted from 0.  Real progress before the failures:
`PreApproxIsoSep`/`BookApproxIsoSep` and their `toBook`/`toSep`/`mono` bridges
are in `ApproxIsometryDefs`; `compSepFwd`, `compSepRev`, and `sepData_comp` are
in `PullbackField`; StepD now has scalar helpers `sepFeed`, `sepNextC0`, and
`sepNextCov`.  Verification passed for the edited Lean files, and the relevant
targeted module builds passed.

Route error #1/3: direct replacement of the D1b hacc step by ordinary
`sepData_comp` is still the wrong bracketing.  `sepData_comp` is valid for
ordinary two-sided composition, but its reverse half follows
`(acc >> step)⁻¹ = step⁻¹ >> acc⁻¹`, putting the one-step data in the F5 `q`
slot.  D1b must keep the already-green half-composition split: forward on the
peel-last `chainComp` ledger and reverse on the peel-first shifted-tail ledger.

Route error #2/3: using the separated carrier while still carrying one scalar
`a` for both `c0` and covariant error collapses back to the old recurrence.
Then `sepFeed a a = a/(1-a)` for positive `a < 1`, so the covariant ledger still
iterates the same bad accumulated transform.

Route error #3/3: keeping two ledgers but bounding both by the old linear
geometric tail is still too weak.  If `c0,cov <= T`, then `sepFeed c0 cov` is
controlled by roughly `T/(1-T)`, so the next covariant ledger has an extra copy
of the accumulated tail that the old one-step tail increment cannot absorb.

Smallest next frontier: prove or state the correct two-ledger scalar budget for
`c0_{n+1} = c0_n + δ_n * (1 + q_n)`,
`cov_{n+1} = q_n + δ_n * B`, `q_n = max (c0_n/(1-c0_n)) cov_n`, with a late-start
choice making both ledgers eventually below `ε` and `1/2`.  After that, replace
the current single-`a` hacc invariant by separated `c0/cov` ledgers and consume
`compSepFwd`/`compSepRev` separately.

## 2026-07-09: separated scalar ledger gate green

Implemented and focused-checked the feasibility-first scalar layer in
`StepDDirected.lean`:

- exact-zero identity carrier `reflSepData :
  BookApproxIsoSep K 0 0 p refl g g`, so the separated induction can start from
  zero ledgers instead of reintroducing a positive book epsilon;
- `sepTail s l = sum_{i<l} (1/2)^(s+i+1)` with both peel-last and peel-first
  recurrences;
- `sepBeta B = max B 4` and the core separated budget lemmas:
  `sepFeed_le_beta`, `sepNextC0_le`, and `sepNextCov_le`.

Verification passed for `StepDDirected.lean`; the only remaining warning is the
expected `exists_directedApprox` endpoint `sorry`.

Gate-3 feasibility audit before editing the large recursion body exposed the
next smallest local API: exact-zero separated data cannot route through the old
`PreApproxIsoDataOn` adapters because those require `0 < eps`.  The hacc
replacement should first add separated versions of the local image-radius,
congruence, and final assembly adapters (`data_image_ball` over
`PreApproxIsoSep`, a separated equality/germ congruence, and
`BookApproxIsoSep.ofParts` or equivalent manual assembly).  This looks like
routine local API work, not a new mathematical obstruction.  After those
adapters check, replace `hacc` with the two-ledger invariant:

- `c0 <= 2 * sepTail s l`;
- `cov <= sepBeta B * sepTail s l`;
- final endpoint wraps with `BookApproxIsoSep.toBook`.

## 2026-07-09: D2 chain split API

Added and focused-checked the target-normalized prefix-tail API used by D2:

- `chainComp_add_apply` gives the pointwise split with the explicit Nat-associativity cast;
- `chainCompAssoc` transports the full chain to target `M ((j+a)+b)`;
- `chainCompAssoc_apply` and `chainCompAssoc_eq` identify it with the prefix followed by the tail.

The dependent cast is handled once in this producer. D2 consumers no longer need to manipulate
`j + (a+b)` versus `(j+a)+b` themselves.
