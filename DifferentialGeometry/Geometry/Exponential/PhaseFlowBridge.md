# PhaseFlowBridge

## Role

This is the thin canonical bridge between the reusable second-order ODE layer
and the moving diagonal exponential's Banach inverse-function linearization.

## Current state

- `freeDiag_eq_unip` identifies `PhaseFlow.freeDiag` with the continuous linear
  map underlying `Exponential.unipotentCLE`.

Focused verification passed without warnings.

## Frontier

Once the geometric phase endpoint is identified with the moving diagonal
exponential, rewrite its `ApproximatesLinearOn` theorem with this bridge and use
the checked small-error producer to construct the explicit inverse branch.
