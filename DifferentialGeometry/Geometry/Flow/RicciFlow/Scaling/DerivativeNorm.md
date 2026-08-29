# First curvature-derivative scaling

## Role

`paraNablaRmNormSq` records the exact parabolic scaling weight of the squared
norm of the first covariant derivative of Riemann curvature.  It is the radius
normalization bridge needed before a unit-cylinder local Shi estimate can be
transported back to a ball of radius `r`.

## Route

The proof uses the invariant covariant-derivative field, the fact that constant
metric scaling leaves the Levi-Civita connection unchanged, linearity of total
covariant differentiation, and the existing tensor norm scaling laws.  It does
not unfold the tensor representation or compare bundle maps.

## Verification

Focused verification passed without warnings.  The theorem uses only the
standard project axioms already present in its import cone; a separate axiom
audit will be done with the completed local-Shi endpoint.

## Next theorem

The next geometric producer is a ball-local Calabi distance comparison
(`dist_calabi_on`, name to be fixed at its canonical comparison layer).  It is
needed to build a moving-ball cutoff from raw support hypotheses.  Only after
that support is available should the analytic producer `shiRm1_cut` consume the
already checked finite-error Bernstein engine.  This scaling theorem is then
the bridge from the unit-cylinder estimate to the radius-`r` statement
`shiRm1_ball`.
