# RoughLaplacian

## 2026-07-10: change-of-trace bound

`trace_sub_le_c0` gives an invariant pointwise estimate for
`tr_h A - tr_g A`.  Under two-sided pointwise metric equivalence with
constant `C`, the trace difference is bounded by

`finrank * C * |h-g|_g * |A|_g`.

The proof uses `exists_diagInv_of_equiv` to choose one common diagonal basis,
collapses the two trace sums explicitly, and applies
`abs_apply_le_sqrt_normSq0S` to both the metric difference and the traced
tensor.  No matrix-inverse calculation, chart assumption, or HCG-specific norm
is introduced.

Focused verification passes.  This producer is complete (100%).  The final
moving-Laplacian `A2` theorem remains unstated and unproved (0%); its dedicated
machinery is approximately 77% complete.
