# ConvFieldLower

## Current status

`ConvOut.lower_of` transfers a sequence-uniform quadratic-form lower bound to
the fixed-window limit metric by order-zero `convPt` convergence.  Positivity
of the coefficient is intentionally not part of this closure lemma; it is only
needed by later completeness consumers.

The implementation introduces no field in `ConvOut` and no endpoint-radius or
global compactness assumption.  Focused verification passed after the owning
lane refreshed the transitive comparison-geometry import chain.

The theorem and its dedicated mathematical machinery are both 100%.  The
unconditional HCG compactness endpoint remains 0%.
