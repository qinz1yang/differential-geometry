# RayAdapted

## Result

`exists_lRayAdapt` is the canonical noncompact producer for a smooth adapted
frame along a strict canonical L-ray.  From `0 < b` and
`b ∈ lRegDomain S T x Z`, it returns one open neighborhood of `[0,b]` and a
terminal-orthonormal family satisfying the square-root adapted equation there.

The theorem was extracted without changing its statement or proof from the
former private declaration in `Monotonicity.lean`.  Its natural acyclic home
depends only on `AdaptedField` and `RayGlobalize`; `Monotonicity` now imports
this module and consumes the single public producer.  No compactness,
completeness, new structure, or supplied producer assumption was added.

## Verification and progress

Focused verification of `RayAdapted.lean` passes without warnings or proof
placeholders.  Its named artifact refresh also passes, and the real downstream
`Monotonicity.lean` then passes focused verification without warnings.  A
`Monotonicity` refresh was not run because its public statements are unchanged.

`exists_lRayAdapt` and this canonical API extraction are **100%**.  This is a
maintenance/API brick rather than a new endpoint proof, so it does not change
the separate accounting for the all-point weak barrier or later P2 capstones.
