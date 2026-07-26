# HmfStateQuad status

## Source theorem

The local-addition quadratic coefficient is state dependent.  The exact
difference therefore has three arms, the new one being

`(Q(u) - Q(v)) (Dv) (Dv)`.

`stateQuadSrcWt` and `stateQuadSrcCarl` prove the corresponding weighted and
Carleson estimates.  On a rough radius-`R` ball, the third contraction arm
costs `L R^2`; it does not use a horizon gain.

The estimate layer imports `RoughCarleson.lean` directly, so its verification
does not wait on either stale-claimed rough fixed-point source file.

## Verification

Focused verification and the named exported-module build are GREEN with no
local warning and no placeholder.  The named build replays two pre-existing
style warnings from `RoughCarleson.lean`; it emits none from this file.  The
check repaired only proof/API shape issues: ordered addition in the base
coefficient bound, the unqualified measurable-ball lemma, and redundant goals
already closed by rewriting.  The exact three-arm constants are unchanged.
This is analytic machinery only; the geometric local-addition coefficient
realization and the forward-uniqueness endpoint remain unproved.
