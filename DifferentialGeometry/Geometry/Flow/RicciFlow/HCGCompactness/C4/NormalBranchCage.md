# NormalBranchCage

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
