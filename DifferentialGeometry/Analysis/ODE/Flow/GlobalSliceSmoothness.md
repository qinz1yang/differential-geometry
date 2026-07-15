# GlobalSliceSmoothness

## Role

This module propagates smooth dependence on initial data along a common compact
time interval for an exact autonomous ODE family. It is generic Banach-space ODE
infrastructure and contains no HCG geometry.

## Verified state

- `orbit_unique_smooth` proves equality throughout an open interval for two
  `C^1` autonomous ODE solutions that meet at one interior time.
- `exists_uniform_flow` extracts one positive smooth restart window over a
  compact set of anchor states.
- `flow_slice_smooth` propagates the smooth identity slice to every interior
  time slice of the exact family.
- Focused verification and downstream use by `NormalPhaseSym` passed without
  local warnings or placeholders.

## Scope

This closes the ODE regularity brick used by the quantitative normal endpoint.
It does not select an inverse branch or prove any HCG radius/containment claim.
