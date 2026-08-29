# CutLocal

## Result

`lExpTime_local` proves that at a nonconjugate point of the positive
L-exponential domain, the joint map

```text
(W, sigma) |-> (lExp S T x W sigma, sigma)
```

is a smooth local diffeomorphism.  Keeping backward time as the second output
makes the total differential block triangular: its time component is the
identity, while its initial-tangent block is invertible by nonconjugacy.

This is the local-coordinate adapter needed in the boundary cut argument to
rule out a second nearby minimizing ray after a limiting initial tangent has
been identified.

## Verification

Focused verification passed without warnings.  The file contains no
placeholder proof.

## Frontier

The joint local-diffeomorphism adapter is complete (100%).  The boundary cut
alternative `lCut_alt` remains unstated and unproved (0%): it still needs a
uniform bound for minimizing initial tangents and a theorem that minimizing
rays remain minimizing under a convergent initial-tangent/time limit.  Those
are separate global/analytic producers and are not consequences of local
invertibility.

`redVolume_anti` remains 0%.  Dedicated compact ordinary-flow L-geometry
machinery remains about 92%; generic manifold inverse-function infrastructure
used here is complete and reused directly.
