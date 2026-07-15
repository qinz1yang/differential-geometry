# CoerciveBilinInverse

## 2026-07-10

Added `IsCoercive.symm_norm_le`: an explicit coercivity inequality
`c * ||v|| * ||v|| <= B v v` gives the Lax--Milgram inverse bound
`||B^{-1} xi|| <= c^{-1} * ||xi||`.

The module also exposes the continuous-covector-facing API used downstream:

- `IsCoercive.sharp` raises a continuous covector through Riesz duality and
  the Lax--Milgram equivalence;
- `IsCoercive.apply_sharp` proves that lowering after raising recovers the
  covector;
- `IsCoercive.sharp_apply` proves the converse lowering/raising identity;
- `IsCoercive.sharp_sub` exposes subtractivity of the sharp operation;
- `IsCoercive.sharp_norm_le` transfers the same explicit inverse bound to
  continuous covectors;
- `IsCoercive.sharp_sub_le` is the two-metric resolvent estimate used to
  control variation of raised Koszul vectors.

This is the first quantitative metric brick for the Route-A moving
inverse-exponential construction.  It is a genuine consequence of the lower
quadratic metric bound, not a new producer assumption.  Focused verification
and the targeted module refresh passed.
