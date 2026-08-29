# Time H1 to C1 upgrade

## Result

`toFun_c1_of_rep` upgrades a time-`H¹` curve to `ContDiffOn ℝ 1` on
`[0,T]` whenever its weak derivative agrees almost everywhere with a
continuous representative `w`.  It also identifies `derivWithin` with `w` at
every point of the closed interval, so the endpoint statements are the natural
one-sided derivatives.

## Route and boundary

The native `timeH1.hasDerivWithinAt_toFun_of_continuousOn` theorem already
implements the FTC step from the integral representation of `u.toFun`.  This
module reuses that producer and Mathlib's
`contDiffOn_succ_iff_derivWithin` characterization on the uniquely
differentiable nondegenerate interval.  No second primitive or weak-derivative
interface is introduced.

The theorem requires only a complete real normed space; finite dimensionality
and an inner product are unnecessary.  It gives closed-interval `C¹` in
Mathlib's within-set sense.  It does not claim a two-sided derivative at the
endpoints or an extension of `w` outside `[0,T]`.

## Status and project position

Focused verification passed without warnings, and the exported module was
refreshed for downstream use.  The generic theorem is complete (100%); its
dedicated C1 assembly is complete (100%) and reuses the previously verified FTC
producer.  Downstream geometric consumption remains 0% in this file.  This is
a small regularity bridge within the roughly 80--84% complete Perelman
L-geometry program.  The terminal `exists_lMinimizer` and `redVolume_anti`
theorems remain 0%.

The source contains no `sorry`, `admit`, or new axiom.
