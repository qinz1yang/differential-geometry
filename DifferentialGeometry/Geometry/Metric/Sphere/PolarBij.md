# PolarBij

## Role

This module packages the ambient polar-coordinate decomposition as the exact
set-level bijection needed by the positive constant-curvature classification
route. It introduces no new structure or consumer assumption.

## Route

- `polar_left_inv` proves directly that `spherePolarInv` recovers a point of
  the open polar cylinder.
- `polar_bijOn` combines that left inverse with `polar_decomp`: direct
  orthogonal norm algebra gives the forward map's codomain, while
  `polar_decomp` gives surjectivity.

The statement shape was informed by Exercise 1.6.20 in the read-only
`frenzymath/Poincare-Conjecture` project. The implementation is native to
`DifferentialGeometry` and reuses only the existing `Polar` API.

## Verification and progress

Focused verification and the exact module refresh both passed without warnings.
The source is `sorry`-free.

`ham3_space_box` itself remains unproved and is therefore 0%. This module is a
completed small producer (100%) in its global sphere-gluing machinery. The
dedicated positive Killing--Hopf topology/global-geometry machinery is
approximately 45% complete; the global two-chart assembly and final
classification theorem remain open. Wider Hamilton positive-Ricci
infrastructure is approximately 80%, and whole HCG compactness infrastructure
is approximately 60%.
