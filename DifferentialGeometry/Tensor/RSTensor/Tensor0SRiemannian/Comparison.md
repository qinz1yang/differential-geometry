# Comparison

2026-07-08: added `normSq0S_le_card_of_component_bound`, a low-layer
component-to-fibre-norm aggregation lemma for covariant tensors in an
orthonormal basis.  This is the correct home for the finite component-sum
bound needed by the volume-comparison radial curvature route; importing the
similar Ricci-flow `StarSum` theorem back into comparison would be the wrong
dependency direction.

Focused verification passed after making the square-bound step explicit:
first convert `|component| <= B` to `|component| <= |B|` using `0 <= B`, then
square both sides.  The targeted module build also passed, so the exported
declaration is available for downstream radial-curvature consumers.

## 2026-07-22 slot-curry Parseval

Added `normSq0S_curry_sum`: in an orthonormal basis, the squared norm of a
rank-`s + 1` covariant tensor is the sum of the squared norms of its first-slot
curries.  It is proved directly from `normSq0S_identity_eq_sum_sq` and the
canonical `Fin.cons` sum decomposition.  Focused and exported verification
passed.

This identity is complete reusable tensor infrastructure.  It does not by
itself advance the complete-noncompact maximum-principle theorem.
