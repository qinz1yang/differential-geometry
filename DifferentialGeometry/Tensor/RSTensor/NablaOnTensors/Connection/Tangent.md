# Tangent.lean Notes

## Goal

Expose the local smoothness fact needed by invariant tensor Ricci-identity
proofs: if the connection is locally `C^1` and `X,Y` are smooth vector-field
sections, then `p ↦ ∇_X Y` is locally `C^1`.

## Result

- Added `CovariantDerivative.smoothSections_cov_contMDiffAt_one`.
- The proof is the same route as the former Levi-Civita-local helper: apply the
  local smooth-connection predicate to the smooth section `Y`, then apply the
  resulting bundle of continuous linear maps to the smooth section `X`.

## Failed

- The first version used `le_top` directly for the smoothness downgrade to
  `∞`; Lean needed the explicit coercion through `ℕ∞`. This was a typeclass
  elaboration issue, not a mathematical issue.

## Verification

- Focused verification passed.

## Lessons

- For smooth sections in this project, inequalities into `(∞ : WithTop ℕ∞)`
  often need the explicit form
  `WithTop.coe_le_coe.2 le_top` after changing to `((⊤ : ℕ∞) : WithTop ℕ∞)`.

## 2026-05-13: Center Tangent-Constant Normalization

- Added `tangentConstInChart_self_continuousLinearMapAt`.
- The lemma says that if a tangent vector at the chart center is first converted
  to the tangent-trivialization model coordinate, then the corresponding
  chart-constant tangent field evaluates back to the original vector at the
  center.
- The proof closes at the bundle trivialization API level with
  `symmL_continuousLinearMapAt`; it does not unfold chart derivatives.
- Verification passed.
