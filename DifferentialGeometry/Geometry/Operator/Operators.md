# Operators.lean - scalar operator algebra

## 2026-06-23

Step C needed the finite-sum algebra behind the center-of-mass gradient
characterization. The reusable result belongs here, below the pointwise
`gradientFun` API, not in the HCG file.

What landed:

- `gradientFun_sum`: the gradient of a finite function sum is the finite sum of
  the gradients.
- `gradientFun_sum_smul`: the gradient of a finite weighted function sum is the
  weighted sum of the gradients.

The proof uses the native function-sum form `sum i in s, f i`, because
Mathlib's `MDifferentiableAt.sum` is stated in that form. Callers with
pointwise lambdas can bridge using `Finset.sum_apply`.

Verification status: focused Lean check and targeted module build passed. Axiom
print for `gradientFun_sum` and `gradientFun_sum_smul` is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by these
declarations. The targeted build replayed existing upstream warnings outside
this file.

## 2026-06-24

Added `gradientFun_eq_zero_of_isLocalMin`: at a local minimum of a differentiable
scalar function on a boundaryless manifold, the realized gradient vanishes.

This theorem belongs in the lower scalar-operator API because
`Comparison/CenterOfMass.lean` needs the first-order gradient fact but should
not import the Laplacian minimum-principle file. The proof is the chart-level
first-order part of the existing Laplacian minimum route, packaged directly for
`gradientFun`.

Verification status: focused Lean check and targeted module build passed.
Axiom print for `gradientFun_eq_zero_of_isLocalMin` is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by this
declaration.

Added `gradientFun_eq_of_flat`: if `(mfderiv f x).toLinearMap` is the
metric-flat covector of a tangent vector `v`, then the realized gradient is
`v`. This is the pure musical-map bridge needed by Step C so the remaining
distance-squared first-variation theorem can be stated as a covector identity,
not as a gradient identity.

Verification status: focused Lean check and targeted module build passed.
Axiom print for `gradientFun_eq_of_flat` is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by this
declaration.

## 2026-07-16

Added the intrinsic logarithm producers needed by the entropy potential lane:

- `gradientFun_log` proves the pointwise gradient chain rule at a positive
  value. Its proof follows the existing `gradientFun_rpow` scalar normal form:
  evaluate through `extDerivFun` and `fromTangentSpace`, then recover the
  tangent vector with metric-flat injectivity. This avoids asking the realized
  scalar tangent fiber to synthesize a ring instance.
- `laplacian_log` proves
  `Delta (log f) = f^-1 Delta f - (f^2)^-1 |grad f|^2` from differentiability,
  positivity, and the existing differentiability of `grad f`. It uses
  `divergence_smul`, the real-power derivative at exponent `-1`, and the exact
  `Real.rpow_two` bridge between real and natural powers.

No chart-selection, compactness, boundary, or new consumer-side convergence
assumption was added. Focused verification passed with no local `sorry`.

Accounting: both named producer theorems are complete (100%).  The downstream
`potential_pde` theorem is separately complete in `PotentialEvolution.lean`;
these producer proofs are not double-counted as completion of that consumer or
of the still-open W-monotonicity and noncollapsing endpoints.

## 2026-07-22

Added `gradientFun_pow`, the natural-power gradient rule in the successor form

`grad (f ^ (n + 1)) = ((n + 1 : Real) * f ^ n) * grad f`.

The successor form is the canonical one for graded cutoff powers: it is valid
when `f x = 0`, needs only pointwise manifold differentiability of `f`, and
avoids the artificial `n - 1` boundary at exponent zero.  The proof is an
induction using the existing `gradientFun_mul`, so it introduces neither a
second power API nor a positivity assumption.

Verification status: focused Lean check passed with no local diagnostics.  No
targeted module refresh was run in this lane.  The named API lemma is complete
(100%); the complete noncompact Bernstein theorem remains separately unstated
or unproved at its final endpoint, and this lemma closes only its graded-cutoff
natural-power gradient seam.

## 2026-07-23

Added the general scalar chain rules:

- `gradientFun_comp` identifies the gradient of `φ ∘ f` with
  `φ'(f) • gradientFun g f`;
- `laplacian_comp` proves
  `Δ(φ ∘ f) = φ'(f) Δf + φ''(f) |∇f|²`.

These are lower, route-neutral operator identities.  In particular, they are
shared by a future smooth parabolic-exhaustion cutoff and by a possible
Calabi-barrier distance cutoff.  They do not assert that either geometric
cutoff exists.

The proofs reuse the canonical manifold derivative and divergence product
rules.  The scalar tangent-fiber normalization in `gradientFun_comp` goes
through `NormedSpace.fromTangentSpace`, avoiding an invalid ring instance on a
real-model tangent fiber.

Verification status: focused Lean check passed with no diagnostics.  Both
named operator theorems are complete (100%).  The solution-generated
`ShiCutoffData` theorem and the corrected complete-noncompact Shi theorem remain
separately at theorem-level 0%; their missing input is geometric/analytic, not
this scalar calculus.

## 2026-07-24

Added `laplacian_add_const`, the neighborhood-local constant-add rule for the
realized scalar Laplacian.  Its hypotheses are the actual first- and
second-order local data used by the proof: eventual differentiability of the
scalar near the evaluation point and differentiability there of its gradient
section.  The proof identifies the two gradient fields on a neighborhood and
uses locality of the covariant derivative; it does not require global
differentiability or a globally smooth extension.

Focused verification passed with no diagnostics.  This operator lemma is
complete (theorem 100%, dedicated machinery 100%).  It closes only the local
constant-add API seam for the Calabi support assembly; `calabiDist_support`
remains a separate theorem-level frontier and is not advanced by this
accounting alone.  No targeted module refresh was run in this lane.

## 2026-07-24: local scalar multiplication

Added `laplacian_smul_at`, the neighborhood-local scalar-multiplication rule
for the realized Laplacian.  It consumes the same honest first- and
second-order germ data as `laplacian_add_const` and avoids requiring a global
smooth extension.

Focused and exact verification are current with no local diagnostics.  This
operator theorem and its dedicated machinery are 100%; the evolving Calabi
support and complete-Shi producers remain separately accounted until their own
files verify.
