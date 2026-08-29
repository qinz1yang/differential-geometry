# CutAlternative

## Goal

Prove the boundary alternative for a compact ordinary Ricci flow: at the last
backward time at which an initial L-tangent is minimizing, either the
L-exponential map is conjugate or another minimizing initial tangent reaches
the same endpoint.

## Route

Approach the cut time from above inside the open positive L-exponential
domain.  At every later time, compact direct minimization gives an initial
tangent reaching the original ray endpoint; maximality makes it distinct from
the original tangent.  Ray-action continuity and the min--max estimate give a
uniform bound for these minimizing tangents.  Finite-dimensional compactness
then yields a convergent subsequence.

The compact-slab continuation theorem puts the limiting ray in the positive
domain.  Fixed-time stability preserves minimizing membership, and joint
continuity of `lExp` preserves the endpoint.  If the limiting tangent were the
original tangent at a nonconjugate cut point, `lExpTime_local` would make the
joint endpoint-time map locally injective, contradicting the distinct later
minimizers.

The theorem uses `IsGreatest` directly for the minimizing-time fiber.  It adds
no cut-time structure, frontier assumption, generalized-flow object, or
consumer-side regularity hypothesis.

## Status

`lCut_alt` passes focused verification without warnings and contains no
placeholder.  Its public assumptions are the compact fixed-manifold flow
context and the statement that `tau` is the greatest point of the minimizing
time fiber.  Its axiom audit reports only `propext`, classical choice, and
quotient soundness.

## Next

`CutInjectivity` now supplies the genuine open injectivity/minimizing domain,
and `CutLocus` supplies the closed measurable tangent cut domain plus the
conjugate/multiple-minimizer image split.  The remaining separate stage is the
measure-zero theorem for that cut image; it must not be replaced by
`interior (lMinDomain ...)`.

## Progress

- `lCut_alt`: 100%.
- Dedicated compact ordinary-flow cut-alternative machinery: about 97%.
- Cut-image measure-zero theorem: 0% until stated and proved.
- `redVolume_anti`: 0%.
- Generic reused compactness, chart, and ODE infrastructure: 100%.
- P2 remains below 1%; the whole Poincare program remains about 3--5%.
