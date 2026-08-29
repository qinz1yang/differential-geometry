# RayEndpoint

This module isolates the endpoint differential and phase-state producers for
the multiple-minimizer cut branch.

`lRayAct_hasFDeriv` proves the full Fréchet derivative of the regularized
L-action with respect to its initial tangent.  Its derivative is terminal
metric lowering composed with the fixed-time differential of `lExp`.  The
proof first obtains differentiability from the local joint `C²` regularity of
the ray Lagrangian and `hasFDerivAt_paramInt`, then identifies every direction
by a common smooth regularized-ray family and `lRegAction_bdry`.

`lRayLag_smooth` exports the stronger native fact behind that local argument:
the fully applied regularized ray Lagrangian is jointly `C∞` in its initial
tangent and square-root time on `lRegJointDom`.  The proof keeps the moving
metric fully applied to the jointly smooth ray velocity, then combines it with
joint scalar-curvature smoothness; no whole bundle or Hom equality is used.

`lRayAct_joint` extends this to the initial-tangent/backward-time parameter
pair.  The action is rewritten near the base point as a fixed `[0,1]`
parameter integral, using the existing smooth time clamp to remain inside one
regular ray family.  Its spatial partial is `lRayAct_hasFDeriv`; its time
partial is the upper-limit fundamental theorem of calculus followed by the
square-root derivative.  Linearity then identifies the joint derivative as
the spatial endpoint covector composed with `fst`, plus the terminal
Lagrangian divided by twice square-root time composed with `snd`.

`lRegAction_bdry` proves that a smooth variation through a central regularized
L-ray with fixed initial endpoint differentiates the regularized action by the
terminal metric pairing.  It is the native square-root-time version of the
endpoint first-variation formula needed to compute a local action branch.

`lRay_phase_inj` proves injectivity of the full terminal phase state: two
regularized L-rays with equal terminal position and velocity have the same
normalized initial tangent.  Consequently `lRay_end_vel_ne` shows that two
distinct rays reaching one endpoint have distinct terminal velocities.  This
uses only ODE uniqueness and does not require minimizing or nonconjugacy
assumptions.

Incremental server diagnostics and final focused verification pass without
warnings or placeholders.  A targeted module refresh is required before the
newly exported `lRayLag_smooth` is consumed downstream.

After `exists_smooth_curve` was strengthened to expose its actual `C∞`
regularity, the order-eight endpoint variation explicitly downgrades that
curve before forming the product parameter map.  This is only an elaboration
compatibility step: the consumer remains `C⁸`, while the reusable curve
producer keeps its stronger canonical conclusion.  Focused verification of
this downstream adjustment passes without warnings.

After `hasFDerivAt_paramInt` was weakened to its actual joint `C¹`
hypothesis, its two callers now explicitly downgrade the available joint
`C²` regularity.  This is also only a compatibility adjustment; the public
ray endpoint statements and their stronger local smoothness producers are
unchanged.  Focused verification passes without warnings.

The fixed-endpoint backward-time derivative, reduced-length derivative, and
strict-region Hamilton--Jacobi identity are now green in `ReducedLength.lean`.
The local `C∞` action germ and the `lActBranch_hess` endpoint-Jacobi identity
are now green in `LocalBranch.lean`.  The next exact consumer is the
fixed-time index comparison `lCost_hess_le` in `ReducedLength.lean`.

Progress accounting: `lRayLag_smooth`, `lRayAct_joint`,
`lRayAct_hasFDeriv`, the endpoint first variation, and terminal-velocity
separation are 100%.  `lActBranch_hess` and its dedicated
local-inverse/Jacobi machinery are verified in `LocalBranch.lean` (100%).
`lCost_hess_le` is a separate downstream theorem and is not counted here.  Compact
ordinary-flow L-geometry machinery is about 99%, reused generic infrastructure
is 100%, and `redVolume_anti` remains 0% until that theorem itself is proved.
