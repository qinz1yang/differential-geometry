# StepCHatReadout status

Status: 2026-07-13, focused verification passed without warnings or `sorry`.

## Checked result

`HasHatCmEqn` records the actual selected-live-slot output: a quantitative
normal branch, its fence, and the branch-native center equation for the filled
finite-hat configuration.

`exists_hat_cm_tail` is the non-transition join of the physical readout route.
It:

- chooses the minimizing coefficient `aMin` before `D`;
- retains the slotwise branch data from `exists_slot_min`;
- intersects that sequence tail with live/dead stabilization;
- exposes the canonical `seqCenterD` radius fact needed by
  `hatPtsCasesComp`;
- obtains the positive active radius from `exists_hat_radius`;
- uses `exists_rad_cage` for one common pair-index threshold;
- builds the actual filled `CenterInput` with `inputOfFillSelf`; and
- applies `exists_hat_cm_eqn` to produce the selected-branch equation.

The theorem adds no endpoint radius field.  `StrictDistInput` is deliberately
the final continuation parameter and remains the independent
Hessian/geodesic-convexity frontier.

## Remaining frontier

The next B/C consumer work is the concrete outer source-slot diagonal: use the
fixed ordered-net source slot `seqCenterD ... beta` and the active ordered-net
target slot `seqCenterD ... alpha`, then feed `hatPtsCasesComp` into this tail
theorem.  The current generic arbitrary-`y` `stepCJoin` interface has no radial
profile and must not be repaired with a new endpoint assumption.

The selected Gates 1--6 machinery is 100%.  Dedicated Step-B/B1 machinery is
about 83%, Chapter 4 machinery about 79%, and whole-HCG machinery remains about
53%.  `StepB1RawInput`, textbook B1, and the conditional Theorem 3.9 endpoint
remain theorem-level 0%.

## 2026-07-13 explicit support-local tail

Added `exists_hat_cm_tail_support`. For a prescribed source slot and arbitrary
`s` contained in its hat, it consumes `WeightDataOn s (fun _ => univ)` and
two-index point convergence only at nonzero weights. It uses
`exists_active_radius` to uniformize the finite target slots, `exists_rad_cage`
to uniformize the finite source branches, builds the filled `CenterInput`, and
calls `exists_hat_cm_eqn_at` for the prescribed source slot. Focused
verification passed without a local `sorry`.

The old POU entrypoint remains unchanged as compatibility API. The remaining
outer B/C frontier is producer-side: construct the finite source cover and fuse
the sparse `InterSlot` transition extraction with the stable-disjoint zero-atom
branch. `StrictDistInput` remains the independent Hessian/convexity frontier.
Endpoint theorem completion remains 0%; this change completes the dedicated
support-local readout machinery only.

## 2026-07-13 outer consumer closure

The producer-side frontier recorded above is now closed in
`StepCProducers.exists_supp_pts_fin` and
`StepCSupportCapstone.exists_supp_cm_fin`.  Each chart-local limit-weight
family is pulled back only to its own source patch, point families alone are
totalized at the ambient finite index, and one finite source maximum produces
the common pair tail. `exists_cm_on_source` then gives an existential source
patch at every point of the global source ball; it does not define a chart
selector.

The approved conditional source-local/global capstone is 100%. Dedicated
Step-B/B1 machinery is about 88%, Chapter 4 machinery about 82%, and whole-HCG
machinery about 54%. `StrictDistInput`/Hessian--Neumann remains independent;
`StepB1RawInput`, textbook B1, and all compactness endpoints remain 0%.

## 2026-07-14 selected-branch Hessian retention

`HasHatCmStrict` now records the same selected source branch together with the
actual root, its invertible center derivative, and the strict local implicit
solution.  `exists_hat_cm_tail_support` uses the normalized-weight field to call
`exists_hat_cm_sol_at` before the quantitative branch data is erased.  The POU
compatibility entrypoint and `HasHatCmEqn` remain unchanged.

Focused verification passes without a local warning or `sorry`.  The sequence
tail, epsilon-dependent active-radius tail, pair-index tail, and finite source
maximum retain their former quantifier order.  No global weight, chart selector,
overlap equality, or endpoint radius assumption was introduced.

The selected-branch Hessian/Neumann support route is 100%.  The independent
`StrictDistInput` producer is still theorem-level 0%; its missing content is the
`lbl413` positive Hessian lower bound and geodesic strict convexity, not IFT
plumbing.  Dedicated Step-B/B1 machinery is about 90%, Chapter 4 about 83%, and
whole-HCG machinery about 55%; `StepB1RawInput`, textbook B1, and compactness
endpoints remain 0%.

## 2026-07-14 direct minimizing readout

This section supersedes the independent-frontier accounting above.
`exists_hat_cm_min` retains `hqAcc`, the full selected branch, and the derived
quarter-ball containment.  It applies the active-radius construction, runs the
finite physical cage once on `3 * rad`, invokes
`HasNormalBrFull.strict_dist`, and returns the center input and selected-branch
strict solution for the fixed intrinsic `minJoin` directly.

The older theorem accepting an arbitrary join and explicit
`StrictDistInput` remains as compatibility API.  No whole-hat target
containment, glued weight, chart selector, overlap equality, or endpoint-radius
assumption was added.  Focused verification and exact target refresh passed.

The support-local `StrictDistInput` and direct minimizing readout producers are
**100%**.  The concrete `StepB1RawInput` producer, textbook B1 theorem, and all
compactness endpoints remain theorem-level **0%**.  Dedicated Step-B/B1
machinery is about **94%**, Chapter 4 machinery about **86%**, and whole-HCG
machinery about **57%**.

## 2026-07-16 prescribed branch data

The primary minimizing readout now returns all four slotwise budgets required
by the moving diagonal branch: `qWide`, `qAcc`, the phase-error threshold, and
the inverse-error coefficient. Older compatibility readouts intentionally
forget them. Focused verification and the targeted refresh passed.

## 2026-07-16 selected branch retention

`exists_hat_cm_min` now retains the eventual `HasLiveBrFull` family alongside
the minimizing readout.  Thus the same chosen `q`, `delta`, branch, fence, and
intrinsic transport data survive past the fixed-stage center equation and can
be consumed by `exists_diag_full`; older compatibility readouts continue to
forget this extra package.

Focused verification and the targeted module refresh passed.  This closes a
producer-data erasure seam, not the moving-reference/all-pairs theorem.
`StepB1RawInput` and textbook B1 remain theorem-level **0%**; dedicated
Step-B/B1 machinery is about **95%**, Chapter 4 about **87%**, and whole-HCG
compactness machinery about **57%**.

## 2026-07-16 selected-center chart membership

`HasHatCmStrictAt` now preserves the selected center's membership in the
source of its normal chart. The lower branch theorem already proved this
membership; the support-local readout merely stopped erasing it. Existing
callers continue to obtain the same strict center equation and derivative data,
with no whole-cage containment or new endpoint-radius premise.

Focused verification and the targeted refresh passed. The concrete
`StepB1RawInput` producer and textbook B1 remain theorem-level **0%**;
dedicated Step-B/B1 machinery is about **98%**, Chapter 4 about **90%**, and
whole-HCG compactness machinery about **60%**.

## 2026-07-18 canonical framed-chart migration

The five fixed-base readouts in `HasHatCmEqn` and `HasHatCmStrictAt` now use
`NormalCoordinates.framedChartAt` at the selected center `x0`.  This matches
the canonical model-space coordinates already returned by
`exists_hat_cm_eqn_at` and `exists_hat_cm_sol_at`; no moving-base chart was
changed.

The first downstream focused check found only a stale Cage artifact.  After
the coordinated exact Cage refresh, the repeated focused check and the exact
module refresh are green, confirming that all three producer calls now consume
the framed interface without a local proof repair.  The
`exists_b1_raw` source proof is complete but is not yet counted exact-green
until that validation passes.  Dedicated Step-B/B1 machinery is about **95%**,
Chapter 4 about **87%**, and whole-HCG compactness machinery about **60%**.
Textbook B1 and the unconditional compactness endpoints remain theorem-level
**0%**.
