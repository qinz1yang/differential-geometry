# PuncturedOverlap

## Role

This sphere-layer producer supplies the connected-overlap input for the
Killing--Hopf two-chart assembly.  It is deliberately independent of the
Cartan map and target manifold.

## Mathematical normal form

`punct2_preconn` states `IsPreconnected` for a unit sphere with two distinct
points removed when the sphere dimension is greater than one.  Stereographic
projection from one deleted point identifies the overlap with Euclidean space
with one point removed, whose path connectedness is already available in
Mathlib.

Only `1 < n` and distinctness of the deleted points are needed.  No
non-antipodal hypothesis and no chart-selector assumption are introduced.
A consumer can install the subtype instance with:

```lean
letI : PreconnectedSpace {x : sphere (0 : E) 1 | x ≠ p ∧ x ≠ q} :=
  Subtype.preconnectedSpace (punct2_preconn hn p q hpq)
```

## Verification and progress

Focused verification and the exact module refresh passed without warnings.

`ham3_space_box` itself remains not started (0%).  Its dedicated
Killing--Hopf machinery is now approximately 75% complete.  This file closes
the local overlap-topology input but does not implement the global two-chart
gluing or the quotient endpoint.
