# GeodesicConvexity.lean

## 2026-07-14 minimizing two-point join

The unconditional intrinsic Hopf--Rinow endpoint
`hopf_rinow_expMapIntrinsic_surjective_minimizing` is now exposed through
`minimizingVec` and `minJoin`.  The checked API records that the selected vector
exponentiates to its target, has Riemannian-distance length, that the joining
curve is continuous with the expected endpoints, and the radial estimate
`minJoin_edist_le`.  Focused verification passed.  The selector and distance
theorems use only the standard logical axioms (`propext`, `Classical.choice`,
and `Quot.sound`); they introduce no project black box.

This closes the routine two-point selector part of the Step-C convexity route.
It does not prove small-ball confinement or strict convexity of
`halfSqDist` along `minJoin`.  The exact remaining comparison frontier is the
`lbl412` Hessian identity together with the `lbl413` positive lower bound on a
cut-locus-free controlled ball.  The existing second-variation layer proves
nonnegativity of the index form for minimizing geodesics, but not the uniform
strict lower bound needed by `StrictDistInput` or the sibling Neumann argument.

Project accounting remains conservative: the minimizing-join selector is 100%,
the `StrictDistInput` producer is still 0%, its dedicated Hessian-comparison
machinery is only at the variation/Hessian-carrier foundation stage, dedicated
Step-B/B1 machinery remains about 88%, Chapter 4 machinery about 82%, and the
whole HCG machinery about 54%.  `StepB1RawInput`, the textbook B1 theorem, and
all compactness endpoints remain theorem-level 0%.
