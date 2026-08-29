# TailActionBranch

## Scope

This module is the analytic producer for the positive-start Calabi branch.  It
does not assume compactness, boundedness below of the action class, or an upper
barrier.  The intended geometric consumer combines it with
`exists_lTail_inj`, `lTail_localDiffeo`, `lRegCosts_bdd_rm`, and
`lCost_le_join_bdd`.

## Source state

`lTailAct_smooth` is source-written.  It proves local smoothness of the actual
fixed-interval regularized L-action of any jointly smooth family on an open
product domain.  The localization is genuine: a finite-dimensional bump keeps
the parameter inside the family domain, a smooth time clamp keeps time inside
the family domain, and the existing parametric interval-integral theorem then
gives smoothness.

`lTailAct_joint` is source-written and warning-free focused green.  For
`a < b`, a jointly smooth
family `alpha` on `V x K`, a fixed start `alpha (A, a)`, family regularity, and
the central L-Euler equation on `[a,b]`, it asserts the joint Frechet derivative
at `(A0,b)` of

```text
(A,r) |-> lRegAction S T (alpha A) a r.
```

The proposed derivative is the fixed-`b` endpoint `mfderiv`, paired with the
central terminal L-velocity by the time-`T-b^2` metric, plus
`lRegLag S T (alpha A0) b` times the endpoint-time direction.  Its private
`tailAct_bdry` helper is the arbitrary-positive-start first-variation boundary
formula: the fixed-start hypothesis kills the initial boundary term and the
central Euler equation kills the residual integral.  The full proof follows
the checked `lRayAct_joint` slice-identification pattern.  A widened smooth time
clamp makes the central curve and its first two germs literal near `a`, `b`, and
the interior; `lRegData_congr` transports the central regular data; a global
smooth parameter curve through each direction identifies the spatial slice;
and the interval-integral right derivative identifies the time slice.

Focused verification exposed only local elaboration details: an interval
change-of-variables equality needed the reverse orientation, an endpoint germ
needed the repository-native `mfderiv_eq` evaluation pattern, the central
endpoint position needed an explicit rewrite, and continuity on `Icc a b`
needed to be restated on `uIcc a b`.  These were repaired without changing the
statement, hypotheses, or proof route.  The new export has not yet received a
named refresh because no downstream module consumes it yet.

`lTailJoint_mfd` is source-written and warning-free focused green.  It
composes `lTailAct_joint` with the native endpoint-time local inverse from
`lTailTime_local`.  Differentiating the inverse identity removes the inverse
differential: if `A_b` is the central terminal velocity and `L_b` the terminal
regularized Lagrangian, the resulting covector sends `(V,c)` to

```text
g_b(A_b,V) + (L_b - g_b(A_b,A_b)) * c.
```

No inverse-derivative identity is assumed from the caller.  The proof uses
`mfderivToContinuousLinearEquiv.right_inv`, splits the joint family derivative
into parameter and time directions, and identifies the latter with
`lVelocity`.  Focused verification required only local elaboration repairs:
the manifold derivative's point precedes its continuous linear map, the time
projection needed a separately inferred congruence, scalar linearity needed an
explicit normalization, and the final subtraction was performed after applying
the metric covector.  None changed the statement, assumptions, or proof route.
The new export has not yet received a named refresh.

`lTailBranch_smooth` is also source-written.  It applies
`lTail_localDiffeo`, restricts the native `localInverse.source` by the
preimage of the action-smooth parameter neighborhood, and returns the actual
tail action as a smooth function on an open endpoint neighborhood.

Before the joint-derivative addition, the module was warning-free focused green
and its named artifact had been refreshed for downstream use.  The only
analytic localization repair needed
during elaboration was the narrow native `BumpClamp` import: its radial bump
keeps the global parameter extension inside `V` while agreeing with the
identity on the smaller ball.  The remaining repairs were dependent tangent-
bundle extensionality and explicit scalar/change-of-variables shapes; no
statement, hypothesis, or geometric route changed.

## Remaining geometric assembly

`exists_lCost_support` is now source-written.  From the canonical minimizing
domain witness, regular backward slab, Riemann-curvature bound, and a positive
start `s0`, it returns an open neighborhood of the minimizing endpoint and a
smooth scalar function which equals L-cost at the center and bounds L-cost
above throughout the neighborhood.

The proof uses `exists_lTail_inj` and the native `localInverse`, then adds the
fixed minimizing head action to `lTailBranch_smooth`.  For each nearby endpoint
it applies `lCost_le_join_bdd`; the required global action lower bound comes
from `lRegCosts_bdd_rm`, not from a consumer assumption.  At the center,
`lRegSol_eqOn` identifies the central family with the minimizing ray, and
`lRegAction_add` plus the `lMinDomain` action/cost equality proves exact
touching.  No `CompactSpace`, caller-supplied `BddBelow`, desired inequality,
frontier wrapper, or placeholder is introduced.

`exists_lCost_support` was warning-free focused green and exported through a
refreshed artifact.  The positive-start endpoint injectivity, native local
diffeomorphism, smooth pulled-back action, and exact spatial upper support are
therefore all **100% theorem endpoints**.  The new joint-action endpoint and
its dedicated derivative machinery (`lTailAct_joint`) are **100% verified** by
a warning-free focused check.  The inverse-composed `lTailJoint_mfd` theorem
endpoint and its dedicated proof are also **100% verified** by a warning-free
focused check.
It adds the time direction at the action
level, but does not yet assemble an all-point spacetime weak upper support for
the reduced-length differential inequality.  That spacetime barrier,
`exists_redLen_le`,
`redVolume_late_low`, `smooth_nlc`, P2, and the final Poincare endpoint remain
**0% theorem endpoints**.  Dedicated L-geometry across the open L8--L9 lane is
about **56--58%**; reused generic
infrastructure is **100%**; the whole P0--P9 infrastructure estimate remains
**15--25%**.
