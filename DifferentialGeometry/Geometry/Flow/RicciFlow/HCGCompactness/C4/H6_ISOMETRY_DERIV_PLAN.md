# H6 isometry-derivative producer plan

## Scope

This lane discharges the [H6] Section 5 content currently represented by the
honest-input predicates `IsometryDerivBounds` and `IsometryDerivBoundsOn`.  It is
independent of the active B/C normal-branch lane: do not edit
`StepBInputs.lean`, `NormalBranchScale.lean`, `NormalBranchMin.lean`, or
`MetricCompactnessInputs.lean` here.

The localized final producers `isom_bounds_on` and `normal_bounds_on` are stated,
proved, and focused-green, so their theorem-level completion is **100%**.
Existing consumers and compactness extraction are already checked; replacing
their older derivative-bound input is a separate B/C integration task.

## Feasible route

The book differentiates the exact coordinate isometry identity.  Formalize the
same recursion in increasing derivative order:

1. **Gate 1: first derivative.**  From
   `g(v,v) <= 2 * ||v||^2`, `(1/2) * ||w||^2 <= h(w,w)`, and
   `h(DPhi v, DPhi v) = g(v,v)`, prove `||DPhi|| <= 2`.
2. **Gate 2: second derivative.**  Differentiate the lowered metric-isometry
   identity once, take the cyclic Koszul combination, and use finite-dimensional
   invertibility of `D Phi`.  This gives
   `D2Phi(u,v) = DPhi (Koszul_g u v) - Koszul_h (DPhi u) (DPhi v)`
   without a separate cross-model Christoffel-naturality theorem.
3. **Gate 3: all-order recursion.**  Use the checked order-three lowered
   recurrence to validate the term shape.  For arbitrary order, express the
   raised Koszul field through the inverse Gram operator and the bounded-linear
   Koszul covector operation.  Differentiate the exact vector identity
   `D2Phi = DPhi * raisedKoszul_g - raisedKoszul_h(Phi, DPhi, DPhi)` and bound
   its product/composition terms with Mathlib's iterated Leibniz and
   Faà-di-Bruno estimates.  The remaining producer is the project-level
   recurrence collecting only lower `Phi` derivatives.
4. **Gate 4: compact-local packaging.**  First package all positive derivative
   orders.  Handle order zero separately from a bounded-image/basepoint anchor,
   then assemble `IsometryDerivBoundsOn`.  Metric isometry alone cannot supply
   the zero-order bound: Euclidean translations are counterexamples.  Derive the
   global `IsometryDerivBounds` form only when both the controlled metric domains
   and this zero-order anchor are global.

Do not introduce a replacement honest-input structure.  Do not differentiate
proof-dependent `IsCoercive.sharp` terms.  The checked `Ring.inverse` Gram API is
the proof-independent smooth representative of the same inverse operation.  If
the exact vector identity cannot be converted into an arbitrary-order bound
using the existing product/composition estimates, the smallest missing
Leibniz/term-collection theorem is the honest Gate 3 frontier.

## Status

- 2026-07-13: Gate 1 is complete and focused-green.  `isom_first_bound` gives
  the project-facing order-one iterated-derivative bound `2`.
- 2026-07-13: Gate 2 is complete at the reusable pointwise level and
  focused-green.  The checked chain is `isom_jet_one` -> `isom_koszul` ->
  `second_eq_koszul` -> `isom_second_eq`; `isom_second_bound` gives the explicit
  bound `6 * CB + 12 * CC`.  `normalTrans_isom`, `normal_fderiv_bij`, and
  `normal_fderiv_le_two` connect the abstract algebra to normal transitions.
- Route-mistake count: **0**.  The implementation needed local Lean repairs but
  no mathematical route was abandoned.
- 2026-07-13: The order-three lowered recurrence `lowered_jet_next` is checked.
  Generic Banach-algebra inverse derivative estimates were extracted to
  `Analysis/Calculus/RingInverseDeriv.lean`; the Gram inverse identification,
  all-order inverse-Gram derivative/application bounds, the bounded-linear
  Koszul covector API, and the fixed-slot `raised_deriv_le` estimate are all
  focused-green.
- 2026-07-13: Gate 3 is complete and focused-green.  `raisedKoszulOp`, the
  product/composition bounds, `isom_rec_le`, `isom_next_le`, and the recursive
  `isomBudget` prove every positive derivative order.  `isom_deriv_le` exposes
  the finite-jet quantifier actually needed at a fixed order.
- 2026-07-13: Gate 4 is complete and focused-green.  `isom_deriv_on` packages
  the open-domain pointwise result; `isom_bounds_on` produces the existing
  `IsometryDerivBoundsOn` predicate using a finite sum of metric-jet constants;
  `normal_bounds_on` supplies the normal-transition specialization.  Its
  explicit target-domain norm bound is the honest independent order-zero
  anchor.
- The final H6 module build is green with no local linter warning.
- Final localized `IsometryDerivBoundsOn` producer theorem: **100% proved**.
  Dedicated H6 Section 5 machinery: **100% for this localized theorem**.
- 2026-07-13: B/C integration is checked through `exists_trans_h6`,
  `existsTransRefH6`, `existsLiveJointH6`, `existsAtomWeightH6`, and the finite
  source-slot `exists_atom_lim`/`exists_atom_fin` diagonal.  The induction
  transports the fixed target-ball containments through every refinement.
  `StepCAtomDiagonal` is presently an unimported leaf with no external caller;
  its abstract `hmapsJ` containment is produced directly with
  `StepBTransitionOverlap.normalTrans_mapsTo` in the checked pair-tail layer,
  so no downstream call site or synonymous map wrapper remained to migrate.
- The S6 compatibility chain, `NormalTransitionDerivBound`,
  `ExpInverseDerivBoundInput`, and the endpoint `expInvDeriv` field were removed
  after a zero-consumer audit.  This migration is 100%.
- `NormalTransAt`/`existsTransTail` give the canonical eventual finite H6
  extractor.  `exists_pair_trans` handles a finite family of positive
  interacting pairs; `InterSlot`, `binter_stable_tail`, and
  `inter_slot_of_binter` select exactly those targets.  Stable-disjoint atoms
  have a checked zero limit, and `atom_trans_small`/`weight_trans_small` prove
  that actual active support lands in the target six-lambda ball.
- `HasAtomWeightLim.binter_of_weight` is focused-green.  It turns a nonzero
  limit normalized weight into eventual `BInter` by pointwise convergence and
  the existing hat-support lemmas.  This is the missing direct bridge from the
  finite atom diagonal to the positive-pair H6 tail.
- **Capstone architecture audit:** the current `hKV0` is quantified on the
  whole canonical cage and every stage.  H6 maps that whole domain only to the
  larger item-3 anchor; cancellation is conditional on reverse-domain
  membership.  The six-lambda theorem is true only on actual atom/weight
  support, and a Euclidean translation example refutes the all-cage inference.
  The selected native route is therefore a support-local decoded-point core,
  followed by `centerAverage.activeFill` at the capstone boundary.  The generic
  arbitrary-compact `hatSrcPtsOfComp` remains unchanged; old whole-cage join
  statements may remain explicit strong-hypothesis compatibility wrappers.
  A stronger later-reference cage is not needed unless this support-local
  implementation exposes a new mathematical obstruction.  Do not derive
  `hKV0` from `normalTrans_mapsTo` or conditional cancellation alone.

Pre-capstone snapshot: localized H6 producer 100%; S6 removal 100%; finite
positive-pair extraction 100%; sparse active-support machinery about 85%;
pair-to-capstone integration about 65%; dedicated Step-B/B1 machinery about
84%; Chapter 4 machinery about 80%; whole HCG machinery about 53%.
`StepB1RawInput`, textbook B1, and all compactness endpoint theorems remain 0%.

- 2026-07-13: the selected support-local consumer is focused-green.
  `hatSuppPtsOfComp`, `unifHatSuppData`, and `hatSuppCageData` work on actual
  nonzero-weight support closures inside compact source-local cages and do not
  reinstate whole-cage target containment. The weight interface uses
  `WeightDataOn ... univ`; `HasAtomWeightLim.weight_data` derives it from the
  existing normalized-weight convergence and stage packages.
- `HasAtomWeightLim.binf_of_weight`, `exists_supp_trans`, and the single
  dependent finite extraction `exists_supp_fin` are focused-green. The latter
  calls the pair extractor once on `Sigma alpha, InterSlot alpha`, so every
  source uses one common subsequence and no interaction subtype is transported
  backwards across refinement.
- 2026-07-13: the approved source-local/global architecture is implemented and
  focused-green. `existsAtomWeightH6_of_innerCover` exposes the actual inner
  cover premise; `exists_live_source_cover` produces the finite chart cover;
  `exists_supp_pts_fin` keeps old-`L` `InterSlot`s and totalizes only the final
  point family; and `exists_hat_cm_tail_support` consumes convergence only on
  nonzero limit-weight support.
- `StepCSupportCapstone.exists_supp_cm_fin` chooses one minimizing scale, one
  divisor, one stable net, and one master subsequence.  It then takes a finite
  maximum over targets inside each patch and a second finite maximum over
  source patches. `exists_cm_on_source` derives the global-ball
  existential-source corollary without a glued weight or chart selector.
- The remaining obstruction is no longer H6 or source-cover wiring.  The
  conditional capstone still consumes `StrictDistInput`; its uniform
  positive-Hessian/full-convexity producer is the independent analytic
  frontier.  The selected-branch Hessian/Neumann and strict-IFT route is
  checked and retained through the capstone.
- The 2026-07-14 audit removes the two-point selector from that frontier:
  `GeodesicConvexity.minJoin` is a focused-green wrapper around the proved
  intrinsic Hopf--Rinow minimizing vector.  `IsNormalDiag.hess_half_inv` now
  proves the branch-native `lbl412` identity.  The actual missing comparison is
  the positive `lbl413` bound; current second variation gives only index-form
  nonnegativity.  No H6 field, endpoint radius, or weight compatibility
  assumption can discharge this gap.

Updated accounting: localized H6 producer 100%; S6 removal 100%; finite
positive-pair extraction 100%; sparse active-support machinery 100%;
conditional source-local/global capstone 100%; dedicated Step-B/B1 machinery
about 90%; Chapter 4 machinery about 83%; whole-HCG machinery about 55%.
`StepB1RawInput`, textbook B1, and compactness endpoints remain 0%.
