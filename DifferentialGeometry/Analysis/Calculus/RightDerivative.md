# RightDerivative

## 2026-08-27

Added the scalar upper-support fencing lemma `le_of_upper_support`.  It uses
continuous induction on a compact interval and a positive level perturbation,
so only points strictly above the target level need a strictly decreasing
right upper support.  This is the generic scalar step needed after a geometric
barrier has been evaluated at a spatial minimizer.

Focused verification passed without warnings, and the named module artifact
was refreshed successfully.  The file contains no `sorry`, `admit`, or added
axiom.
