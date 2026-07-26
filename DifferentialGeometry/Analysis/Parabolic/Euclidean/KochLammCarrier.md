# KochLammCarrier

## Route decision

The completed carrier is the closure, inside `KLPathData`, of exact smooth
compatible path data.  A core datum includes a bounded continuous value field
on the closed slab, a smooth space-time representative agreeing with it, and
the existing three-arm `KLPath` bounds for the representative and its actual
spatial Frechet derivative.

This route is shorter than spelling out the full closed graph directly.  The
direct graph would immediately require compatible restriction maps between all
dependent `Lp` cylinder germs, overlap equality, and stability of the weak
integration-by-parts identity.  Those facts are still needed at the later
heat-realization boundary, but they are not prerequisites for completeness.

The closure retains the data needed by the nonlinear and heat layers:

- the value arm remains an actual bounded continuous field;
- gradient products can be defined cylinderwise on the two `Lp` germ arms and
  extended using the proved Koch--Lamm product estimates;
- a heat/Duhamel map can be extended from the dense smooth core after its
  Koch--Lamm Lipschitz estimate is proved.

The carrier itself does not claim that an arbitrary completed point already
satisfies a classical derivative identity.  The later heat-realization theorem
must pass the derivative and PDE identities to the norm limit.  This keeps the
analytic frontier explicit rather than encoding it as a carrier hypothesis.

## Implemented content

- `klSpaceDeriv`: the genuine spatial Frechet derivative of a space-time
  field;
- `KLSmoothPath`: exact smooth compatible core data;
- `KLPathCore`: its range in the complete norm-data ambient;
- `KLPathSpace`: the closure subtype;
- completeness and density of the core inclusion.

No global `Nonempty` instance is added.  A later fixed-point ball has a
specific smooth initial datum and can use its `KLSmoothPath.toSpace` image as
the base point; a separate overloaded-zero construction is not part of the
minimal carrier API.

## Verification state

- Focused Lean check: passed with no local warnings.
- Completed compatible carrier: proved and focused GREEN.
- Heat/Duhamel extension and distributional realization: 0% as theorems.
- `ricci_flow_forward_unique`: 0%.
