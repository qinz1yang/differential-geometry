# SolutionResidual

## Purpose

Produce the arbitrary-dimensional, globally fixed residual field in the
commuted curvature equation directly from `IsSolutionOn`.

## 2026-07-22 canonical all-order producer

`rmResidualField S t k` is defined recursively before any point or frame is
chosen: level zero is `e0Field`, and the successor is the canonical
`resStarNext` built from the covariant derivative, fixed spatial commutator,
and fixed Christoffel-time correction fields.

`rmResidualField_cost` gives the exact constructor-tree certificate

```text
StarSum2Cost Idx S t k (rmResidualField S t k)
  (rmResidualCost (card Idx) k).
```

The private supplied-frame induction `rmResidual_local` proves the component
heat identity on one smooth orthonormal patch.  Public `rmResidual_cost` then
chooses the single residual field first and only afterward chooses, for every
point, a canonical smooth orthonormal frame and its pointwise basis.  Thus the
public quantifier order is the required

```text
exists T, cost T and forall x, exists basis, derivative identity.
```

The legacy dimension-three `resStarSol` remains as a compatibility endpoint;
the new direct tower does not depend on it.

Source assembly contains no `sorry`, `admit`, or new axiom.  Focused
verification is GREEN with no local warning, and the exact target is current
(`9564/9564`).  Thus `rmResidual_cost` is theorem-level **100% checked** and its
dedicated producer machinery is **100%**.  The direct tower is also exact-current;
the complete noncompact Shi theorem remains theorem-level **0%** until the
independent solution-produced `ShiCutoffData` frontier is closed.
