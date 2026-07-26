# PhaseFlowPerturbation

## 2026-07-10: generic phase-flow perturbation producer

Completed:

- `phaseField` lifts an acceleration `a (x,v)` to the first-order phase field
  `(v,a (x,v))`.
- `phaseField_lip` proves that a `κ`-Lipschitz acceleration gives a
  `max 1 κ`-Lipschitz phase field on the same phase-space set.
- `phaseErr` records the explicit time-one coefficient
  `κ * exp (1 + κ) * (exp 1 - 1)`.
- `phase_pos_res_le` proves the pairwise time-one position residual bound for
  two exact phase trajectories.  It first applies phase-space Grönwall to
  control the full trajectory separation, then applies the existing
  second-order Grönwall theorem to the position difference after subtracting
  its free linear evolution.
- `freeEnd` and `phase_pos_approx` package that pairwise bound directly as an
  `ApproximatesLinearOn` theorem for a family of exact trajectories.
- `freeDiag` retains the initial position, and `phase_diag_approx` upgrades the
  same estimate to the diagonal time-one map `(x,v) ↦ (x, endpoint)`.  This is
  the analysis-layer form of the unipotent approximation needed by the
  moving-diagonal exponential branch.

The theorem hypotheses remain honest: the phase-space Lipschitz estimate,
trajectory regularity, exact ODE identity, initial condition, and domain
membership are all explicit.  No geometric realization or flow existence is
hidden in this analysis-layer file.

Verification passed for the focused file check, with no warnings and no
`sorry` declarations.

## Progress accounting

- `phaseField_lip`: 100% complete.
- `phase_pos_res_le`: 100% complete.
- `phase_pos_approx`: 100% complete.
- `phase_diag_approx`: 100% complete.
- Generic time-one phase-flow perturbation brick: 100% complete.
- Quantitative moving inverse theorem: unstated and unproved (0%).
- Its dedicated machinery is conservatively about 56% complete after this ODE
  producer; the remaining work includes geometric acceleration realization,
  uniform phase-domain closure, and integration with the chosen inverse branch.
- Step-B/B1 machinery is about 66% complete; whole-HCG machinery remains about
  47% complete.  These infrastructure percentages do not count as theorem
  completion.

## 2026-07-10 follow-up

- Added `freeDiagCLE`, with apply/coercion lemmas, as the canonical continuous
  linear equivalence underlying `freeDiag`.
- `DiagExpDerivative.unipotentCLE` is now a compatibility alias to this lower
  analysis-layer object, so the quantitative inverse and the existing diagonal
  derivative use exactly the same linear map.
- Focused verification passed.  The earlier progress estimate above is
  superseded by the live B1 plan; the quantitative model inverse is now checked,
  while the intrinsic B1 producer and theorem remain 0%.
# Phase-flow perturbation

## Free inverse readout

`freeDiagInv_apply` records the explicit inverse of the free retained-endpoint
equivalence: `(x, y)` is sent to `(x, y - x)`.  This small canonical simp lemma
supports quantitative fixed-endpoint inverse-velocity estimates without
unfolding `freeDiagCLE` downstream.  Focused verification passed.
