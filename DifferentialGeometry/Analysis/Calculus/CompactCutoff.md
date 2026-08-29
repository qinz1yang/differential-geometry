# Compact cutoffs

## Implemented surface

`exists_bump_nhds` constructs a globally smooth, compactly supported real
cutoff that is identically one on a neighborhood of a supplied compact subset
of a finite-dimensional Hausdorff manifold. It uses finitely many native
`SmoothBumpFunction`s and the formula `1 - ∏ i, (1 - b i)`.

The theorem does not require `SigmaCompactSpace`: compactness of the target set
provides the finite subcover, and the finite union of the individual supports
is compact.

## Verification

Focused verification and the targeted module export pass without warnings.
The result is reused by the compactly supported tangent-bundle flow in the
generic fixed-endpoint field-realization theorem.
