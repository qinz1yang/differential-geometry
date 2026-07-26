# NormalPhaseSmallness

## Role

This module closes the numerical small-parameter bridge between the normal
metric jet bounds and the strict error threshold required by a quantitative
inverse theorem.

## Current state

- `normalPhaseK_zero`, `normalPhaseK_cont`, and `normalPhaseK_lim` show that
  the explicit acceleration Lipschitz polynomial vanishes continuously with
  the velocity radius.
- `normalPhaseErr_lim` composes this with the generic phase error limit.
- `normalPhaseErr_lt_ev` gives the eventual strict bound below every positive
  threshold.
- `NormalRadiusProfile.phaseRadius` chooses one quarter of the checked relative
  radius floor; `phaseRadius_metric` and `phaseRadius_exp` place its ball inside
  both the normal-metric control region and the quarter exponential ball on a
  fixed distance sublevel.
- `exists_normal_q_lt` selects a positive `q` for any positive ordinary radius
  and any positive endpoint-error threshold.  Its conclusions are exactly the
  two numerical hypotheses of `NormalPhase.exists_normalFlow`, together with
  the requested error bound at velocity radius `2q`.
- `NormalRadiusProfile.exists_phase_q` specializes that selection to
  `phaseRadius`.  Combined with `phaseRadius_metric` and `phaseRadius_exp`, it
  supplies every radius and numerical input needed by `exists_normalFlow` on a
  fixed distance sublevel.
- `NormalRadiusProfile.exists_phase_scale` makes the selection relative: it
  chooses global positive coefficients `aq` and `aδ`, then for every `R ≥ 0`
  takes `q = aq * mu R`.  The result satisfies the stronger bilateral-flow
  fences `6q < phaseRadius` and
  `3 C (2q)^2 ≤ (2/3)q`, stays below the inverse threshold, and proves the
  quantitative target-radius lower bound `aδ * mu R ≤ δ`.

Focused verification and the targeted module build passed for the complete
API, including the relative-scale producer and its profile specialization,
without local proof or style warnings.

## Frontier

The small-radius numerical selection, profile containment, and proportional
target-radius lower bound are complete.  The next consumer is a fixed-`q`
`normalDiagAt` worker in `NormalPhaseEndpoint`, followed by the transported
`DiagInvBranch` package.  `StepB1RawInput` and textbook B1 remain unstated and
0%; this numerical-selection substage is 100%, but it only advances their
dedicated machinery.
# Normal phase smallness

`NormalRadiusProfile.exists_phase_scale` now selects the forward phase error
below `T / (2 * (N + 1))`, where `N` is the norm of the free inverse and
`T = N⁻¹`.  It retains the resulting quantitative inverse error strictly
below one while preserving the previous target-radius lower bound.  This is
an internal scale tightening, not a new endpoint hypothesis.  Focused
verification passed.

## 2026-07-18 framed-radius migration

`phaseRadius_exp` now targets `expRadiusGp / 4`, matching the canonical framed
normal-coordinate profile.  Focused verification and the module refresh
passed.  The theorem still consumes `NormalRadiusProfile`; it is not its
producer.
