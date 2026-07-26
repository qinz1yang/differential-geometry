# FibreEquiv

## Role

This file is the purely topological fibre/fundamental-group layer for covering
maps and the local path-space universal cover.

## Current producer

`finite_pi1_of_uc` packages the standard argument at the chosen base point:

1. a compact universal cover has finite covering fibres;
2. the base fibre is equivalent to the fundamental group by monodromy;
3. finiteness transports across that equivalence.

The theorem uses only separation, connectedness, local path connectedness,
semilocal simple connectedness, and compactness of the universal cover.  It has
no Riemannian metric, manifold-chart, or chart-basis assumptions.

The file's imports were narrowed to its actual topological dependencies.  Its
only downstream repository consumer already imports its geometric dependencies
directly.

## Verification

Focused verification passed, and the exact `FibreEquiv` module artifact is
current.  The new theorem introduces no `sorry`; its axiom audit reports only
the standard quotient/classical axioms already used by the path-space model.

## Project position

This compact-cover finiteness producer is complete (**100%**) and is a small
supporting component of the `ham3_space_box` machinery.  `ham3_space_box`
itself remains unproved (**0%**), as does the theorem-level broader Hamilton
endpoint while that producer is open.
