# `AdaptedIndex.lean`

## Result

`lIndex_smul_pt` gives the reusable pointwise expansion for multiplying an
adapted field by an arbitrary differentiable real scalar `f`.  Besides the
scaled native index density, the formula records the exact `(deriv f)^2`
moving-norm term and the `-2*s*f*(deriv f)*Ric` cross term.  The
positive-start weight `(s-a)/(b-a)` and the original zero-start weight `s/b`
are therefore instances of one canonical identity rather than parallel
calculations.

`lIndex_adapted_pt` gives the exact pointwise Morgan--Tian expansion for the
endpoint test field `W(s) = (s / b) P(s)`.  Under the adapted equation for
`P`, its regularized index density is the sum of the scaled density of `P`,
the moving-norm term, and the explicit Ricci correction.  This uses only the
native regularized-index and Ricci-sharp APIs; it introduces no Hamilton-type
scalar or time-Ricci derivative interface.

`lIndex_adapted` integrates this formula on `[0,b]`.  It carries separate,
honest interval-integrability hypotheses for the scaled index-density and
Ricci terms, and uses `lAdapted_inner_eq` to identify the moving-norm integral
with the terminal scalar `|P(b)|^2 / (2*b)`.  Its remaining integral is exactly
the scaled native index density minus the Ricci correction, ready for the
later finite trace contraction.

## Verification and project status

All three declarations passed focused verification without warnings or
placeholders.  The implementation reused the existing regularized-index
algebra and did not duplicate the moving-metric cancellation.

The generic scalar-multiple and zero-start single-field identities are 100%.
The positive-start finite trace and weighted Hamilton integral remain separate
theorem endpoints until their own declarations verify.  The all-point
spacetime barrier, `exists_redLen_le`, `redVolume_late_low`, `smooth_nlc`, P2,
and the final Poincare theorem remain 0%.  Dedicated L-geometry across open
L8--L9 is about 55--57%, reused generic infrastructure is 100%, and whole
P0--P9 infrastructure remains 15--25%.
