# HigherOrder.lean Notes

## What Worked

- Added the model-space total covariant derivative for covariant tensors:
  `totalCovDeriv_tensor0SModelAt`.
- The apply theorem `totalCovDeriv_tensor0SModelAt_apply_cons` verifies the
  intended convention: the new derivative slot is first, and evaluating it at a
  model vector recovers the existing directional formula
  `covariantDeriv_tensor0SModelAt`.
- Added DifferentialGeometry-facing realization predicates:
  `TotalNabla0SRealizes`, `TotalNablaRSRealizes`,
  `HigherCovDeriv0SRealizes`, and `HigherCovDerivRSRealizes`.
- The higher-order predicates keep regularity explicit. They do not claim that
  iterated covariant derivatives automatically produce smooth bundled fields.

## What Failed

- A bundled model definition
  `totalCovDeriv_tensorRSModelAt : TensorRSModel r s -> TensorRSModel r (s+1)`
  was attempted. Lean checked the idea locally but timed out while verifying
  linearity in the input covariant tensor argument for the bundled
  continuous-linear map.
- The timeout was proof elaboration/performance, not a mathematical obstruction.
  The existing mixed directional formula is still used through the realization
  predicate `TotalNablaRSRealizes`.
- A targeted compiled build crashed during code generation before
  `suppress_compilation` was added. The file is proof/interface oriented, so
  suppressing compilation is appropriate.

## Remaining Proof Risks

- The mixed model total derivative should be closed later by introducing small
  reusable continuous-linear maps for the three terms instead of assembling the
  whole map in one proof block.
- The current higher-order API deliberately stores derivative slots as `k + s`.
  This is the LaTeX `(r, s+k)` convention with derivative slots first, and it
  avoids non-definitional casts in the recursive constructors.

## 2026-05-11 bridge update

- Added apply lemmas for `TotalNabla0SRealizes` and `TotalNablaRSRealizes`, so
  users can expose the directional `nabla0SFun` / `nablaRSFun` formulas without
  unfolding the predicates.
- Added `higherCovDeriv0SRealizes_two_apply` as the narrow second-derivative
  evaluation bridge needed by one-form endpoint work.
- Attempted constructor lemmas for `HigherCovDeriv0SRealizes` at `k = 1` and
  `k = 2`; the math was trivial, but the `k + s` output casts made the public
  theorem shape fragile.  They were not kept.  Prefer apply/consumer lemmas
  until a cleaner cast-normalization helper is introduced.

## 2026-05-11: Removed analytic realization layer

- `TotalNabla0SRealizes`, `TotalNablaRSRealizes`, `HigherCovDeriv0SRealizes`, and `HigherCovDerivRSRealizes` now quantify over smooth tensor fields and vector-field sections instead of analytic/top regularity.
- This matches the proved `nabla0S_reg` / `nablaRS_reg` output regularity and avoids forcing downstream LC/Bochner code to manufacture analytic sections.
- Verification passed.

## 2026-05-13: Definition 14.5 agreement

- Removed the stale `suppress_compilation`; the higher-order interface now
  compiles normally.
- Added `TotalNabla0SRealizes.eval_smooth_slots`, which evaluates a supplied
  total covariant derivative realization on smooth moving slots and rewrites it
  to the tensorial Definition 14.5 rule.
- The theorem is a consumer wrapper around `nabla0SFun_eval_smooth_slots`, so
  the higher-order API now exposes the derivation rule without unfolding its
  realization predicate.
- Verification passed.

## 2026-05-13: Tensor-level total derivative constructor

- Added the canonical pointwise constructor
  `totalNabla0SFun : (0,s) -> (0,s+1)` using the existing model total
  derivative and the new chart-linear connection endomorphism.
- Added explicit regularity and bundled-field wrappers:
  `TotalNabla0SRegular` and `totalNabla0S`.
- Added `totalNabla0SFun_apply_tangentConstInChart`, which checks the model
  centered chart formula directly.
- Added the iterated constructor `totalNabla20S` and the valence-normalized
  wrapper `totalNabla20S_succSucc`.

## Remaining Frontier

- `totalNabla0SFun_apply_section` is the single remaining certification lemma:
  contracting the tensor-level total derivative with an arbitrary smooth vector
  field should recover the old directional `nabla0SFun`.
- This is an API proof frontier, not a mathematical obstruction.  The centered
  model-slot formula is already proved; the missing step is the fixed-chart
  comparison between an arbitrary section value and its model coordinate inside
  the old directional implementation.

## Verification

Verification passed with the expected frontier warning.

## 2026-05-13: Contraction frontier attempt

- Tried the centered comparison route for `totalNabla0SFun_apply_section`:
  rewrite arbitrary inputs through base-point tangent trivialization, compare
  the new total-nabla model expression against `fixedChartNabla0SModel`, then
  use `nabla0SFun_apply_selfChart_slots`.
- The attempt exposed the real missing helper more precisely.  The old
  `fixedChartNabla0SModel` uses Mathlib's self-chart tangent coordinate
  convention where the centered `mpullbackWithin` reduces directly to `X x`,
  while the new proof route was mixing that with
  `trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x (X x)`.
- The next lemma should be a small tangent-coordinate normalization at the
  center, proving the relevant `connectionEndomorphismInChartL` application
  after rewriting both `extChartAt_to_inv` and
  `mfderiv_extChartAt_self`.  This should be proved in the connection/tangent
  layer before retrying the tensor theorem.
- Verification passed after restoring the single documented frontier.

## 2026-05-13: Post-normalization Retry

- The connection-layer blocker was discharged in `Connection/Endomorphism.lean`
  by centered comparison lemmas for `connectionEndomorphismInChartL`.
- Retried `totalNabla0SFun_apply_section` using the centered formula comparison:
  `totalNabla0SFun_apply_tangentConstInChart`,
  `fixedChartNabla0SModel_apply_slots`, and
  `nabla0SFun_apply_selfChart_slots`.
- The proof still did not close cleanly.  The exact remaining blocker is the
  self-chart tensor-input normalization: after unfolding the tangent-constant
  slot at the center, Lean produces goals of the form
  `fderivWithin (extChartAt I x) ... v = v`.  This should be factored into a
  small tangent-coordinate lemma before another retry.
- The file was restored to the single documented frontier
  `totalNabla0SFun_apply_section`.
- Verification passed with the expected frontier warning.

## 2026-05-13: Tangent-constant Self Lemma Retry

- The tangent input normalization from the previous retry was discharged in
  `Connection/Tangent.lean` by `tangentConstInChart_self_continuousLinearMapAt`.
- Retried `totalNabla0SFun_apply_section` with explicit model coordinates
  `Xmodel` and `slotsModel`, so the tangent-constant input side and the
  centered `mpullbackWithin` direction both normalize correctly.
- The proof narrowed further but still did not close.  The exact remaining
  blocker is now the center tensor-model equality inside the correction sum:
  Lean needs a reusable lemma identifying
  `tensor0SModelInChart s x (fun y => α y) (extChartAt I x x)` with
  `tensor0SModelAt s x x (α x)` as model tensors, not only after ad hoc
  unfolding inside a large goal.
- The file was restored to the single documented frontier
  `totalNabla0SFun_apply_section`.
- Verification passed with the expected frontier warning.

## 2026-05-13: Total-nabla Contraction Closed

- Added the missing fixed-chart center model lemma in
  `FixedChart/Models.lean`.
- Proved `totalNabla0SFun_apply_section`.  The proof uses model coordinates for
  the first slot and tensor slots, compares the total-nabla model formula with
  `fixedChartNabla0SModel`, and then returns through
  `nabla0SFun_apply_selfChart_slots`.
- The public realization theorem `totalNabla0S_realizes` now depends on a
  proved contraction theorem rather than a `sorry`.
- Verification passed.
