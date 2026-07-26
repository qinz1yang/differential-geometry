# KochLammData

## Purpose

This file builds the complete ambient norm-data spaces for the exact
Koch--Lamm cylinder norms.

For every admissible center and radius, a coordinate stores the corresponding
local `Lp` germ after multiplication by its scale factor.  Mathlib's dependent
`lp` space at exponent `∞` takes the supremum of these coordinate norms and is
complete even though the cylinder index is not finite.  The value arm is a
bounded continuous function on the closed slab.

The resulting ambient types are:

- `KLPathData`: value plus scaled `L²` and late `L^(n+4)` gradient germs;
- `KLSrc0Data`: scaled `L¹` and late `L^((n+4)/2)` source germs;
- `KLSrc1Data`: scaled `L²` and late `L^(n+4)` flux germs.

The finite ball constants in the predicate layer are `NNReal`; their real
coercions are therefore the exact finite bounds for these `lp ∞` norms.

## Honest boundary

Completeness of these ambient products is not yet completeness of realized
paths.  A closed compatibility graph must still assert that all cylinder
germs arise from one field and that the path's gradient germs are its weak
spatial derivative.  That is the next carrier producer; no heat mapping
estimate or derivative realization is hidden in this file.

## Verification state

- Source for the ambient types and three completeness theorems: complete.
- Focused Lean check: pending until the immediately upstream
  `KochLammSpaces` export finishes; the theorems are not yet counted as
  proved.
- Realized compatible carrier: 35% (ambient complete, closed graph missing).
- Endpoint `ricci_flow_forward_unique`: 0%.
