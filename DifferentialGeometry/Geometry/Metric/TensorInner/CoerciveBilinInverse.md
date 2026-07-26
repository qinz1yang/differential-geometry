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

## 2026-07-15

Added `IsCoercive.sharp_eq_inverse`.  It identifies the existing
Lax--Milgram/Riesz `sharp` operation with `Ring.inverse` of Mathlib's canonical
Gram operator `InnerProductSpace.continuousLinearMapOfBilin`.  This gives the
metric-spray layer a proof-independent total expression without introducing a
second Gram API; coercivity is used only to identify that total expression with
the geometric sharp map.  Focused verification passed.

## 2026-07-19

Source-written two minimal moving-form interfaces:

- `IsCoercive.sharpCLM` packages `sharp` as a continuous linear map from the
  Hilbert dual to the primal space, and `sharpCLM_norm_le` gives the operator
  norm bound `||sharpCLM|| <= c^{-1}` from the explicit quadratic coercivity
  constant;
- `IsCoercive.sharp_var_le` is the joint resolvent estimate when both the
  bilinear form and the covector vary.  It splits the difference into a
  covector arm controlled by `sharp_norm_le` and a form arm controlled by the
  existing `sharp_sub_le`.

These are the invariant mass-matrix inverse and continuity estimates needed
before applying the existing time-dependent finite-dimensional ODE theorem in
the HMF Galerkin lane.  They do not assert HMF existence and introduce no new
assumption or class.

The shared named build still owns the Lean slot, so this 2026-07-19 addition is
source-reviewed but not yet focused-checked.  Earlier verification claims in
this note refer only to the pre-existing declarations.
