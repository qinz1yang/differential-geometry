# CalabiBranch

## Result

`exists_lTailFamily` extracts from the arbitrary-time phase flow a jointly
smooth family of regularized L-curves with fixed position and varying actual
square-root-time velocity at an arbitrary regular time.  Unlike the canonical
zero-time family, the seed velocity is not rescaled by a factor of two.

`lTailFamily_step_of` glues such a family across one neighboring interval from
a supplied uniform local phase flow, and `lTailFamily_step` obtains that flow
from the native arbitrary-time ODE theorem.  Both preserve the fixed position
and the actual velocity parameter at the positive start time.

`lTailFamily_extend` is the global continuation producer: along any prescribed
regular L-solution on a connected open interval, it uses compact uniform phase
existence and an open/closed argument to extend the velocity family from the
positive start time through any chosen later time in that interval.

`lTailLine_deriv` identifies differentiation along an affine velocity line
with the endpoint family's manifold differential.  For an actual-velocity
family, `lTailLine_dstart` computes the initial covariant derivative as the
chosen velocity direction, while `lTailLine_jacobi` proves that the resulting
variation field is a regularized L-Jacobi field and vanishes at the fixed
positive start.

`exists_lTail_germ` gives a smooth global curve-and-field representative after
a smooth clamp to a compact tail.  This is useful local extension machinery,
but it deliberately does not claim that the globalized field lies over the
original curve away from the tail; therefore it is not by itself the global
test field required by the index-form contradiction.

## Role in the Calabi route

These are the positive-start suffix existence and continuation producers.  In
particular, evaluation of the family from `lTailFamily_extend` at the chosen
later time is now the required smooth suffix endpoint map, without changing
the semantics of `lExp` or `lActBranch`.

It does not yet prove that a minimizing suffix endpoint differential is
invertible.  The differential and Jacobi bridges are now complete.  The next
exact producer is a suffix-relative index contradiction: an endpoint-kernel
direction gives a nonzero Jacobi field vanishing at both suffix endpoints, and
a global smooth test field along the original minimizing curve must convert it
to a negative broken index.  The existing `IsLConj` and `lIndex_neg_conj` are
zero-base APIs and do not directly provide this relative result.

## Verification and progress

Focused verification passes without warnings or placeholders, and the named
module artifact has been refreshed.  The local positive-start family, its
one-step continuation, and its continuation through a prescribed regular
suffix are complete (100% each); the affine-line differential, initial
derivative, and Jacobi-field bridges are also complete (100% each).  The suffix
endpoint local inverse, all-point spacetime weak upper barrier, and
`exists_redLen_le` remain unstated and unproved (0%).  This file is dedicated
positive-start Calabi machinery only.  In the current whole-plan accounting,
`redVolume_anti` remains complete (100%), dedicated L-geometry including the
open L8--L9 endpoints is about 48%, and the generic infrastructure reused here
is complete (100%).
