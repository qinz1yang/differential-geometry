# Tensor0SMetricDeriv.lean — moving-metric norm derivatives

## New canonical inverse-metric derivative

`basisInv_time` proves the fixed-basis identity

`∂ₜ g⁻¹ᵢⱼ = -∑ₐ,ᵦ g⁻¹ᵢₐ (∂ₜg)ₐᵦ g⁻¹ᵦⱼ`

directly for the canonical `basisInvMetric`.  Its only analytic input is
componentwise `HasDerivAt` for the metric pairings
`(g t).inner x (basis i) (basis j)`.  It does not assume differentiability of
inverse components, a coordinate inverse formula, a flow equation, or a local
chart.

## Route that worked

The proof realizes a finite coefficient array as the continuous linear map on
coordinate columns.  `basisInvMetric_real` makes the canonical inverse array a
two-sided inverse of the metric Gram operator.  Mathlib's Banach-algebra
derivative of inversion (`hasFDerivAt_ringInverse`) then gives
`-g⁻¹ gdot g⁻¹`; evaluation on `Pi.single j 1` and at coordinate `i` gives the
scalar theorem.

The time-dependent coefficient array deliberately uses the normal form
`Idx → Idx → Real`, not the reducible synonym `Matrix Idx Idx Real`.
`Matrix` carries a specialized topology in this checkout, while the derivative
route needs the finite-Pi norm topology; asking Lean to treat the whole moving
array as a normed `Matrix` exposes that topology diamond.  Matrix notation is
therefore used only for static algebraic helper statements, never as the
codomain of the time curve.

The first attempted implementation also used `Matrix.mulVecLin` and whole
matrix multiplication.  That made instance selection choose pointwise function
multiplication after reduction.  The checked proof instead defines the finite
sum action explicitly and proves the two inverse-composition identities from
the two fields of `basisInvMetric_real`.

## Verification

GREEN: the focused check passed without warnings or `sorry`.

## Honest frontier accounting

- `basisInv_time`: complete (100%).
- The future invariant producer discharging the entropy consumer's
  `hgrad_deriv`: theorem not yet stated/proved (0%); its dedicated machinery is
  about 15%.  This file closes only the inverse-metric derivative brick; the
  fixed-base derivative of `df`, component product rule, and invariant
  identification remain.
- The broader entropy/noncollapsing machinery is about 59%; Perelman's
  no-local-collapsing endpoint theorem itself remains unstated/unproved (0%).
- The whole HCG compactness project is about 60%.  This helper is
  infrastructure and must not be counted as endpoint completion.

## Rank-one invariant closure

`ricReact_one` identifies the rank-one coordinate reaction with the invariant
quantity `2 * Q(A♯, B♯)` for the canonical inverse metric.  Its public statement
does not ask the consumer for inverse components, their symmetry, or a basis
realization hypothesis.  The proof collapses `Fin 1 → Idx` with the unique-slot
equivalence, expands both sharped covectors, and uses symmetry of
`basisInvMetric` only inside the proof.

`normSq_one_time` then hides the remaining finite-basis bookkeeping.  From the
invariant assumptions `∂ₜg = -2Q` and the slotwise derivative of a moving
one-form, it proves

`∂ₜ |A|² = 2 Q(A♯, A♯) + 2 ⟨Ȧ, A⟩`.

The useful proof normal form was to preserve the scalar result of
`map_update_sum` before rewriting updated slot functions.  Rewriting the slot
functions too early lost the scalar-pulled normal form and made the same algebra
appear harder than it is.  No whole tensor or whole Hom equality is used.

Verification is GREEN for the complete file, and the explicitly refreshed
module is also GREEN.  The only remaining linter messages belong to pre-existing
declarations, not the new rank-one theorems.

## Updated honest accounting

- `ricReact_one`: complete (100%).
- `normSq_one_time`: complete (100%).
- The generic invariant rank-one moving-norm machinery: complete (100%).
- The operator specialization `normGradSq_time`: complete in its own module,
  but the existing entropy consumer has not yet been rewired to derive its
  `hgrad_deriv` field from this producer.
- The concrete reversed-Ricci-flow and potential-time regularity inputs needed
  for that rewiring remain separate work; the Perelman no-local-collapsing
  endpoint theorem remains unstated/unproved (0%).
- Broader entropy/noncollapsing machinery remains about 59%; the whole HCG
  compactness project remains about 60%.
