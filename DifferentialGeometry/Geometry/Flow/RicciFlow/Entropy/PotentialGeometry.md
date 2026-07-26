# PotentialGeometry

## 2026-07-16 density-amplitude identities

The checked producers are:

- `potential_grad`: `grad f = -u^{-1} grad u` for a positive smooth density;
- `potential_grad_sq`: the corresponding squared-gradient identity;
- `potential_square`: the pointwise logarithmic potential for `u = v^2`;
- `square_pot_energy`: `v^2 |grad f|^2 = 4 |grad v|^2`.

All statements are pointwise and invariant.  They use no frame, tensor
representation equality, compactness, or flow assumption.  The existing
`potential_pde` consumer now reuses the squared-gradient producer.  Focused
verification passed without warnings or a new `sorry`.

This amplitude bridge is **100%**.  It is machinery for the fixed-metric W
estimate; `w_fixed_lower`, no-local-collapsing, and `ham3_noncollapse` remain
theorem-level **0%**.
