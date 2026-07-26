# CartanTransfer.lean

## Role

This module is the lowest-layer scalar ODE transfer step in the positive
Killing--Hopf / `ham3_space_box` route.  It compares Jacobi fields on two
possibly different manifolds after fully applying them to matched parallel
orthonormal frames.

## Status

- `jacobi_coord_xfer` is implemented without new geometric assumptions or a
  whole-fiber identification.  Its only cross-manifold hypothesis is equality
  of the scalar curvature matrices seen by the two supplied frames.
- The proof applies `ode2_pi_zero` directly to the coordinate differences,
  using `parInner_deriv`, `parInner_d2`, and `parInner_curv_expand`.
- Focused verification passes without warnings, and the exact module artifact
  is current.

## Honest progress

- `ham3_space_box`: 0% (the endpoint theorem is still unproved).
- This scalar cross-manifold Jacobi-coordinate producer: 100%.
- Dedicated positive Killing--Hopf machinery: about 20%; the next substantial
  phase is to supply the matched radial frames and curvature coefficients, then
  turn coordinate equality into exponential-map differential inner-product
  transfer.
