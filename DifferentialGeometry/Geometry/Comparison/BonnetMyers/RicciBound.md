# RicciBound.lean

## 2026-07-17 global Rm bound to lower Ricci bound

Added `ricciLower_of_rm`.  It combines the existing orthonormal-component
estimate for the canonical Ricci tensor with the geometric Rayleigh bound to
show

`sqrt (normSq Rm04) <= Rm  =>  Ric >= -(n^2 * Rm) g`.

Focused verification passed, and the module refresh passed.  This closes the
curvature-to-Ricci-lower-bound input needed before Bishop--Gromov; it does not
prove relative volume monotonicity or a packing bound.

The theorem is complete.  The Bishop--Gromov endpoint remains 0%; its dedicated
V2 infrastructure is only about 3--5% complete.
