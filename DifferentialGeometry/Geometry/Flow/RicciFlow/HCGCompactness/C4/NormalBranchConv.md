# NormalBranchConv

## Role

This file packages matched finite-stage and limiting normal diagonal branches,
including forward and exact-inverse convergence on common balls.

## Verified state

- `HasDiagPairConv` is the checked output package shared by the branch and
  live-slot consumers.
- `NormalRadiusProfile.exists_diagPair_at` accepts a prescribed positive stage
  radius `q` with the retained phase-radius, acceleration, forward-error, and
  inverse-error budgets.  It uses `q / 2` as the limit radius and returns
  `HasDiagPairConv` with those exact radii.
- The limit error bounds are obtained by `normalPhaseK_mono`,
  `PhaseFlow.phaseErr_mono`, and `PhaseFlow.invErr_mono`; no second radius is
  selected.
- `exists_diagPair_conv` retains its established public statement and remains
  available to consumers that still select the two radii internally.
- The live source theorem `MetricCompactnessInputs.exists_slot_diag` consumes
  `exists_diagPair_at` after one finite-family metric-limit extraction.  Its
  statement keeps the original `LiveSlot L` index, uses the slotwise exhaustion
  radius `L.rInf alpha + 1`, and returns exact radii
  `(q alpha, q alpha / 2)` without another subsequence or chart selector.

Focused verification passed without local warnings.
The `exists_slot_diag` inspection recorded here was read-only; this note did
not run verification for `NormalLiveConv.lean`.

## Frontier

The slotwise metric-convergence and prescribed-branch seam is now implemented
in the live source.  The next integration step is for the higher producer to
supply the `q`, phase-radius, acceleration, forward-error, and inverse-error
families coming from the live minimizing-branch scale.  Those hypotheses align
directly with `exists_slot_min`.

One branch-identity seam remains: `exists_slot_min` retains a stage branch
inside `HasNormalBrFull`, whereas `exists_slot_diag` calls
`exists_diagPair_at` and independently chooses the stage `e` and
`deltaStage`.  A common radius does not identify existential witnesses.  Before
the convergence package is used by the minimizing support/readout, a producer
must either reuse the retained stage flow/branch or prove on-domain equality
and transport the fence/branch data.  This is an API-coherence gap, not an
objection to the mathematical statement of `exists_slot_diag`.

## Project position

- Prescribed-radius matched branch producer (`exists_diagPair_at`): proved,
  100%.
- Live-slot prescribed-radius integration: implementation present in
  `exists_slot_diag`; not independently verified by this note.
- `StepB1RawInput` producer: unstated/unproved, 0%.
- Step B/B1 infrastructure: about 75%.
- Whole HCG compactness infrastructure: about 50%.

## 2026-07-16 selected-stage branch transfer

This section supersedes the branch-identity frontier above.
`HasDiagPairConv.congr_stage` transfers both forward and exact-inverse
convergence from the canonical stage branch to any other fenced
`IsNormalDiag` branch with the same source radius.  It uses
`IsNormalDiag.eqOnSource` and shrinks only the internal inverse comparison ball
to fit both available target radii; it adds no endpoint-radius assumption.

`NormalRadiusProfile.exists_diagPair_at` now also retains
`NormalDiagFence` for every canonical finite-stage branch.  Together these
outputs let the live producer align convergence with the exact branch already
stored in `HasLiveBrFull`.  Focused verification and the targeted module
refresh passed.

The branch-coherence brick is complete, but the uniform moving-reference and
all-pairs comparison-map producers are not.  `StepB1RawInput` and textbook B1
remain theorem-level **0%**; dedicated Step-B/B1 machinery is about **95%**,
Chapter 4 about **87%**, and whole-HCG compactness machinery about **57%**.
