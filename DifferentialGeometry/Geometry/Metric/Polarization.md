# Polarization

## Current state — 2026-07-23

`inner_eq_of_diag` is the fiberwise real polarization bridge used by Cartan
local-isometry arguments.  A continuous linear map that preserves
`g.inner x u u` for every tangent vector also preserves `g.inner x u v`.

This is pure pointwise metric algebra.  It adds no curvature, completeness,
connectedness, or manifold-global hypotheses.

## Progress accounting

- `inner_eq_of_diag`: complete and focused verification passed.
- The planned Cartan local-isometry theorem remains unstated (0%); its dedicated
  Jacobi/exponential machinery is approximately 25%.
- `ham3_space_box` itself remains open (0%); its dedicated
  Killing--Hopf/quotient machinery is approximately 20%.
