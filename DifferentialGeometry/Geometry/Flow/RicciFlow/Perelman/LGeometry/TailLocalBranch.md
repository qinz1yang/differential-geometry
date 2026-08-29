# TailLocalBranch

## Source result

`lTail_localDiffeo` is source-written.  It takes the actual jointly smooth
family map on `V × K`, an interior central velocity, a terminal time in `K`,
and injectivity of the endpoint manifold differential at that velocity.  It
then proves a genuine `C∞` `IsLocalDiffeomorphAt` for the terminal endpoint
slice.

The proof follows the native `lExp_localDiffeo` route rather than introducing a
new inverse predicate.  Finite-dimensional injectivity gives surjectivity of
the endpoint continuous linear differential, hence a continuous linear
equivalence.  The chart derivative is invertible, the order-one manifold
inverse function theorem produces a local diffeomorphism, and the native
infinity-order upgrade supplies the final local inverse.  Consumers therefore
receive the standard `localInverse`, open-source, left/right-inverse, and
smoothness APIs already attached to `IsLocalDiffeomorphAt`.

`lTailTime_local` is also source-written.  It assumes the family is jointly
smooth on an open product `V × K`, that `(A0, b)` lies in that product, and
that the fixed-`b` endpoint differential is injective at `A0`.  It concludes
that `(A, r) ↦ (alpha (A, r), r)` is a `C∞` local diffeomorphism at
`(A0, b)`.  The proof is the native block-triangular route from
`CutLocal.lExpTime_local`: the second differential component recovers the time
direction, and the remaining kernel equation is exactly the supplied
fixed-time injectivity hypothesis.  No time derivative of `alpha` is required
to be invertible.

No ODE, minimizing, compactness, inner-product, nonzero-dimension, separation,
or sigma-compactness assumption is added: those facts belong to the producer
of the actual family and endpoint injectivity, not to the inverse-function
step.

## Tail-action follow-up

The former noncompact join obstruction is resolved below this module:
`lCost_le_join_bdd` supplies the honest infimum comparison and
`lRegCosts_bdd_rm` derives its lower-boundedness input from the canonical
curvature bound.  Parameterized tail-action smoothness and endpoint-inverse
composition now live in `TailActionBranch.lean`; this module remains the
pure inverse-function step.

## Verification and progress

The focused check covering both `lTail_localDiffeo` and `lTailTime_local` is
warning-free GREEN.  The joint theorem needed one explicit finite-dimensional
instance for each product tangent model before the standard
injective-implies-surjective step; no mathematical or API assumption changed.
It uses only the inverse function theorem import and adds no compactness or ODE
dependency.  A named refresh remains deferred until a downstream module
actually consumes the new export.

`lTail_localDiffeo` and `lTailTime_local` are both complete (100%).  The
all-point spacetime weak barrier,
`exists_redLen_le`, `redVolume_late_low`, `smooth_nlc`, P2, and the final
Poincare endpoint remain separate theorem endpoints and are still 0% until
their own declarations are proved.

## Terminal-slice compatibility

`lTailInv_slice` is source-written below the two local-diffeomorphism
constructions.  It states that, near the central terminal endpoint, the first
component of the joint endpoint-time local inverse on the slice `(y, b)` agrees
with the fixed-`b` endpoint inverse built from the same family and central
velocity.

The proof uses only native local-inverse structure.  The joint right-inverse
identity first forces its second coordinate to equal `b` and its endpoint to
equal `y`.  Continuity of the joint inverse restricts to a neighborhood where
its first coordinate lies in the target of the fixed local inverse; the fixed
left-inverse identity then gives uniqueness.  No equality of chosen inverses,
inverse-derivative formula, minimizing input, or new wrapper is assumed.

The focused check is warning-free GREEN.  `lTailInv_slice` is therefore a
complete theorem endpoint (100%).  No named refresh was run: a downstream
module should first be source-written to consume the new export.  The all-point
spacetime weak upper support, `exists_redLen_le`, `redVolume_late_low`,
`smooth_nlc`, P2, and the final Poincare endpoint remain separate theorem
endpoints and are still 0% until their own declarations are proved.
