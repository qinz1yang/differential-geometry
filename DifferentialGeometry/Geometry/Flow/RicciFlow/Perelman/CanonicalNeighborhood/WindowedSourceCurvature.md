# WindowedSourceCurvature

Chapter25 source-only continuation of good-point derivatives. Initially unverified.
No compiler/artifact/root action during Chapter23's exclusive slot.

For eps at most 1/4, the fixed model ball of radius 2 and fixed time window
[-4,0] fit inside the actual witness comparison. Transfer the earlier model
bound to its image using WindowedWitnessTransport and the native curvature-norm
naturality lemmas in GoodPointDerivatives. Preserve the constant
sourceCurvatureBound 3 K = 9*(10+2*K)+1. Do not construct an old KappaModelWitness
or assume an equivalence of the two witness records.

This purely spatial step includes the terminal slice and needs no regularity
of the source time set. The subsequent Shi application still must supply a
regular interior slab and pass its derivative bounds to the terminal slice.
The earlier model-curvature bound remains an explicit input, not a newly
proved Chapter23 result.

## Verified 2026-09-11

Final saved check 3 EMPTY (25.7s), named build 1 passed (32.4s), SHA256 67f03ce7064062b6188acae4f9c1b7b1d1ee9b5c99fbcc4c9676320a82259c1e. The fresh WindowedGoodPointAxioms1 audit covers all23 publics in20.8s:22 standard-only; only book_good_point_derivatives inherits the named earlier Chapter23 model-curvature obligation. Frozen completion receipt: E:/lean-tools/chapter25-book-20260910/windowed-good-point-completion.json. This supersedes the initial unverified status above.

