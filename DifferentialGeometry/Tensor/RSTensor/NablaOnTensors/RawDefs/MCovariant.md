# MCovariant.lean

## 2026-07-10 mixed model projection

- Added `TensorLieDeriv.modelAt_mcovRS`, the fixed-chart model projection for
  `mcovariantDeriv_tensorRSWithin`.
- The proof reuses `tensorRSModelAt_trivializationAt_symm`; it does not unfold
  `TensorRSSpace` or the Hom-bundle representation.
- Focused source verification passed.
- This projection producer is complete.  Its immediate consumer is the
  `hleft_model` bridge in `Regularity/Derivation.lean`; that consumer now uses
  the projection and has also passed focused verification.
- This is a small API/performance repair inside the tensor layer; it does not
  change theorem completion for Hamilton compactness.  Whole HCG machinery
  remains about 45%, with the compactness endpoint theorems at 0%.
