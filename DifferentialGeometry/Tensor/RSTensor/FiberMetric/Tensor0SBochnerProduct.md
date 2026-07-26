# Tensor0SBochnerProduct

## 2026-07-22 covariant-tensor Kato bound

Added `normSq0S_du_le`, the general pointwise estimate

`|d|T|²|² ≤ 4 |T|² |∇T|²`

for a covariant tensor field with realized total covariant derivative and
realized differential of its squared norm.  The proof composes `du_norm0S`,
the invariant fibre Cauchy--Schwarz inequality, and the orthonormal
slot-curry Parseval identity.  It adds no curvature, compactness, completeness,
or cutoff assumptions.  Focused and exported verification passed.

The theorem itself is complete.  It is one input to the complete-noncompact
Bernstein localization; that capstone remains theorem-level 0%.
