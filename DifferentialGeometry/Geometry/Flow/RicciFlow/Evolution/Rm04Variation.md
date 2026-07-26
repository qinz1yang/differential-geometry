# Rm04Variation

## Role

This module owns the arbitrary-dimensional normalization of the lowered-Riemann
time derivative from coordinate Christoffel-variation derivatives to an
explicit `\nabla^2 Ric` right-hand side.

## Status

`rm04VarRHS` and `rm04Var_of_sol` are focused-check GREEN.  The public
`rm04Var_of_sol` inputs now use the canonical coordinate family
`nablaRicComp (coordinateFrameAt x₀)`, exactly matching `coordNab2Reg` and
`coordGammaMix`.  The proof consumes the checked `realizedRmBase_timeDeriv`,
derives its elementary metric/Ricci spatial regularity inputs from the
canonical frame packages, and rewrites both Christoffel-variation terms with
the checked Gamma-coordinate bridge.

The lower `realizedRmBase_timeDeriv` API still names the explicit
`ricciCovDerivCompInFrame` family.  This module bridges that compatibility seam
locally using the existing `coordNablaRealOn` equality on the open coordinate
domain.  The transport is applied both to the mixed-derivative witness and to
the final covariant derivative of the Christoffel RHS; it introduces no new
assumption or public wrapper.

The canonical-signature migration is focused-check GREEN with no diagnostics.
Its first check exposed only the expected hardcoded lower-producer seam; the
coordinate-domain transport above closed it.  This source change has not
received a targeted artifact refresh in this lane.

The remaining Hamilton-base work is downstream assembly rather than a
coordinate-normalization issue: combine this time-variation theorem with the
checked static Hamilton identity in the dedicated flow producer.

## Project accounting

- `rm04VarRHS` / `rm04Var_of_sol`: 100% implemented and focused-verified; the
  changed canonical signature still needs its coordinated artifact refresh.
- Arbitrary-dimensional flow-level Hamilton base producer theorem: not yet
  completed in Lean, hence 0%; its dedicated supporting machinery is
  approximately 80--85% complete after this normalization and the
  exact-current static identity.
- The arbitrary-dimensional complete-Shi analytic lane remains infrastructure
  work; its public HCG-facing theorem is still unstated/unproved.
- `CurvBoundInput.movingShi_open`: 0%; its analytic producer chain remains open.
- Whole HCG compactness endpoint theorem: 0%.
