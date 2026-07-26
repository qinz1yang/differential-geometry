# PolarPD

## Role

This module packages the explicit round-sphere polar formulas as an honest
smooth partial diffeomorphism.  It is dedicated machinery for the
`ham3_space_box` positive constant-curvature classification route.

## Route

- The source direction is the unit sphere in the orthogonal complement of the
  pole.  Thus the open cylinder is an open set in
  `ℝ × sphere (0 : (ℝ ∙ p)ᗮ) 1`; it is not incorrectly treated as an open
  subset of `ℝ × E`.
- The target is the relative open subset of the ambient unit sphere obtained
  by deleting the pole and antipode.
- `polar_bijOn` supplies the inverse identities.  Smoothness is proved from
  `spherePolar_smooth` and `polarInv_smooth`, using the native analytic sphere
  manifold instances and open-subtype restriction.
- `spherePolarPD` exposes the resulting `C∞` `PartialDiffeomorph`, with exact
  source, target, and application lemmas.

No local-isometry, exponential-map, or global-classification assumption is
introduced.

## Verification and progress

Focused verification and the exact module refresh both passed without warnings.
The source is `sorry`-free.

`ham3_space_box` itself remains unproved and is therefore 0%.  This file is a
completed small producer (100%) in the punctured-sphere/global-gluing phase.
The dedicated positive Killing--Hopf machinery is approximately 60% complete:
the local Cartan partial isometry and smooth polar partial diffeomorphism now
exist, while identifying them on overlaps and carrying out the global
two-chart gluing remain substantive frontiers.  Wider Hamilton positive-Ricci
infrastructure is approximately 80%, and whole HCG compactness infrastructure
is approximately 60%.
