# PhaseFlowSmallness

## Role

This module supplies the small-parameter selection interface for the phase
endpoint error used by quantitative inverse-function arguments.

## Current state

- `phaseErr_zero`, `phaseErr_cont`, and `phaseErr_tendsto` show that the
  endpoint error vanishes continuously with the acceleration Lipschitz
  coefficient.
- `phaseErr_lt_ev` packages the eventual strict bound below any positive
  threshold.

Focused verification and the targeted module build passed without local proof
or style warnings.

## Frontier

Compose this result with the normal-coordinate polynomial coefficient
`normalPhaseK h R` as `R -> 0`, then choose a common positive phase radius whose
error lies below the inverse norm of the unipotent linearization.
