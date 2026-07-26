# NormalBranchCage

## 2026-07-18 canonical framed-cage migration

- The selected-branch cage now uses `framedChartAt` at every fixed center.
  All 35 former raw-chart occurrences in this module were fixed-base chart
  coordinates; no moving-base inverse-tangent readout occurs here.
- The retained phase quarter-ball is now stated directly with
  `expRadiusGp / 4`, matching `phaseRadius_exp`; the obsolete
  `expMapC2Radius / 4` target was not recovered through a false comparison.
- `HasNormalBrFull.exists_cm_eqn`, `HasNormalBrFull.exists_cm_deriv`, and the
  prescribed/live-slot readouts therefore consume the canonical framed
  `StepCCmDomain.centerReadoutB_min` interface without a conjugation wrapper or
  a new radius assumption.
- Focused verification is green with zero diagnostics, and the exact module
  refresh is green.  The framed Cage producer interface is now available to
  downstream readouts.

The concrete `MetricCompactBase.exists_b1_raw` proof body is complete, but its
canonical framed dependency validation is still in progress; the separately
named textbook B1 theorem and unconditional compactness endpoints remain
theorem-level 0%.  Current rounded infrastructure accounting is about 95% for
B1, 87% for C4, and 60% for the whole HCG compactness project.

## Role

This module is intended to combine the center/point cage ledger with one
selected quantitative branch for the whole finite configuration.

## Verified state

- `seqCenterD_rInf_lt` identifies the totalized center distance with the ordered
  net radius and places it eventually below `rInf gamma + 1`.
  `liveCenters_rInf` finite-intersects this slotwise statement.
- `exists_slot_min` calls `normalMinScale` once, before `D` is chosen.  The same
  positive `aMin` is then specialized to every `LiveSlot` at
  `Rgamma = rInf gamma + 1`, retaining the full minimizing branch, the metric
  radius bound, and the non-strict half-radius `expRadiusGp` floor.
- `lamInf_lt_halfMin` converts the one-shot physical budget
  `8 * exp C < aMin * D` into the strict slotwise half-margin
  `4 * lamInf gamma < (aMin * mu (rInf gamma + 1)) / 2`.
- `exists_rad_cage` takes a finite supremum of the positive slot margins.  One
  common pair-index threshold then places every active-point radius inside the
  physical cage for every stabilized live slot.
- `HasNormalBrFull.exists_cm_eqn` re-encodes the actual point family in the
  selected normal chart and applies the minimizing readout using the checked
  non-strict `expRadiusGp` floor; it returns the branch fence and the actual
  `chartCmEqnB = 0` equation.
- `HasNormalBrFull.exists_cm_deriv` uses the same physical cage to retain the
  actual root, its invertible selected-branch center derivative, and the strict
  local implicit solution.  The result stays on the branch already carried by
  `HasNormalBrFull`.
- `aliveSlots_tail`, `hat_mem_live`, and `hat_dist_centerD` make the finite-hat
  routing dead-slot aware: a positive POU weight forces the chosen hat slot to
  be live and supplies its canonical four-`lamInf` distance bound.
- `exists_hat_cm_eqn_at` is the source-local readout: a prescribed
  `alpha : LiveSlot` together with membership in its hat and its slotwise cage
  inequality supplies the corresponding minimizing-branch fence and center
  equation.  It does not select a target weight and makes no assertion about
  compatibility between different source charts.
- `exists_hat_cm_sol_at` is its quantitative sibling.  With the normalized
  weight sum it retains the root, invertible derivative, and strict local
  solution for the prescribed source slot; it does not select an active target
  slot or alter the radius ledger.
- `exists_hat_cm_eqn` keeps the previous API as a corollary.  It selects a
  positive-weight slot, proves it live, and delegates the geometric readout to
  `exists_hat_cm_eqn_at`.

Focused verification passes for both source-local and compatibility entrypoints,
without a local `sorry`.

## Frontier

The fixed-stage physical finite-hat readout and selected-branch
Hessian/Neumann/strict-IFT output are closed.  The independent missing input is
`StrictDistInput`: the cage inequalities do not prove the `lbl413` positive
Hessian lower bound or geodesic strict convexity.

No endpoint radius assumption was added.  The selected minimizing-branch
Gates 1--6 machinery and this fixed-stage branch/Hessian sub-brick are 100%.
`StrictDistInput`, the concrete `StepB1RawInput` producer, textbook B1 theorem,
and compactness endpoints remain theorem-level 0%.  Dedicated Step-B/B1
machinery is about 90%, Chapter 4 machinery about 83%, and whole-HCG
compactness machinery about 55%.

## 2026-07-14 quarter-ball and strict-distance closure

This section supersedes the open-frontier paragraph above.  `exists_slot_min`
now retains an eventual containment of the whole selected Euclidean `rho` ball
in `normalQuarter`.  The containment is derived from the already selected
`q`-scale, `hqWide`, `hqMin`, and `phaseRadius_exp`; it is not a new input or
endpoint-radius assumption.

That retained quarter-ball tail is consumed by
`HasNormalBrFull.strict_dist`, which closes the former `StrictDistInput`
frontier with the physical `R + 6 * rad < rho / 2` cage.  Focused verification
and exact target refresh passed.  The next honest B/C frontier is the concrete
`StepB1RawInput` producer.  That producer, textbook B1, and the compactness
endpoints remain theorem-level **0%**; dedicated Step-B/B1 machinery is about
**94%**, Chapter 4 machinery about **86%**, and whole-HCG machinery about
**57%**.

## 2026-07-16 slotwise prescribed-radius retention

`exists_slot_min` now carries `qWide`, `qAcc`, the phase-error threshold, and
the inverse-error bound together for every live slot. These were existing
outputs of the global scale selection; the live-cage theorem now preserves
them through its finite slotwise specialization. Focused verification and the
targeted refresh passed. No endpoint radius field was added.

## 2026-07-16 full live-branch predicate

`HasLiveBrFull` is the compact recurring predicate for one stage: every
`LiveSlot` carries the exact `HasNormalBrFull` selected branch, including its
fence and intrinsic transport data at the physical minimizing scale.  It is a
packaging predicate over existing output, not a new branch construction or
assumption.  `exists_hat_cm_min` produces it eventually, and
`exists_diag_full` preserves it at every refined index before transferring
canonical convergence onto the selected branches.

Focused verification passed; downstream checked consumers confirm the exported
predicate.  `StepB1RawInput` and textbook B1 remain theorem-level **0%**;
dedicated Step-B/B1 machinery is about **95%**, Chapter 4 about **87%**, and
whole-HCG compactness machinery about **57%**.

## 2026-07-16 center chart-source retention

`HasNormalBrFull.exists_cm_deriv` and its prescribed-slot strict-center
consumer now retain that the selected center itself lies in the source of the
target normal chart. This fact was already proved as `hcSource` in the
branch calculation and was previously discarded before the stage-map readout.
No radius or branch assumption was added.

Focused verification and the exact upstream refresh passed. This is a
producer-data retention brick for the actual global stage map, not completion
of `StepB1RawInput`: that producer and textbook B1 remain theorem-level
**0%**. Dedicated Step-B/B1 machinery is about **98%**, Chapter 4 machinery
about **90%**, and whole-HCG compactness machinery about **60%**.
