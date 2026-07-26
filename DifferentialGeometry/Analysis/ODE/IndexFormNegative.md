# IndexFormNegative

## 2026-07-24

The canonical negative split construction is now parameterized by an arbitrary
terminal time `L`.  The endpoint-aware test field is owned by
`indexTestFieldTo` / `indexTestDerivTo`; `indexForm_test_to`,
`indexForm_pos_to`, and `IsJacobiSolOn.exists_split_neg_on` carry the
proof on `[0,L]`.  The former unit-interval declarations remain compatibility
wrappers at `L = 1`.

Focused verification passed without diagnostics.  The arbitrary-length split
theorem is 100% at theorem level and its dedicated ODE machinery is 100%.
The globally smooth arbitrary-length negative direction remains the immediate
downstream theorem in `IndexFormNegativeSmooth`.

## 2026-07-23

This module continues Route B, N-d, at the abstract Jacobi ODE layer.

`IsJacobiSolOn.snd_ne_zero` converts the interior zero-data uniqueness theorem
into the form used by the conjugate-point argument: a nontrivial Jacobi
solution vanishing at an interior time has nonzero velocity there.  Continuity
of the coefficient on the compact interval supplies the bounded-coefficient
hypothesis automatically.

The module also defines the polynomial field
`indexTestField q t = t(1-t)q` and proves the exact cross-term identity
`indexForm_test`, together with its strictly positive form
`indexForm_test_pos`.

`exists_split_neg` is the intended next endpoint: on the two intervals
`[0,c]` and `[c,1]`, it perturbs the truncated Jacobi field by the same
polynomial test field and makes the sum of the two index forms negative.  The
two pieces agree in value at `c`; no global smoothness is claimed.

`contDiffOn_jacobi` and `jacobi_pair_contDiff` bootstrap two-sided Jacobi ODE
data on an open interval to arbitrary smoothness.  `exists_smooth_split`
combines that bootstrap with `exists_split_neg`, returning the two smooth
half-fields with their actual derivatives in the index forms.

Focused verification through `exists_smooth_split` passed without warnings,
and the targeted module build passed.
The remaining frontier is geometric realization and a
minimizing-geodesic nonnegativity theorem that accepts two matching smooth
halves.  The existing in-tree nonnegativity theorem accepts only one globally
smooth field, so it cannot yet consume this honest cornered witness.

There are two mathematically sound continuation routes:

1. Smooth the matching half-fields across a shrinking interval using
   `Real.smoothTransition`, prove uniform derivative bounds from `y c = 0`,
   and show the global index form converges to the negative split sum.
2. Extend the geometric second-variation theorem to two smooth halves, as in
   the broken-variation reference route.

No existing project theorem directly supplies endpoint-preserving `H¹`
smooth approximation on an interval.  Choosing between these routes is a
substantial architecture decision rather than a local proof repair.
