# Regularized L-action minimizers

## Role

`ActionRegMin.lean` packages the relaxed direct-method minimizer on a positive
normalized interval `[0,b]` as an endpoint-honest `IsLRegCurveOn` witness.  It
keeps the exact attained `lRegCostC1` value and the genuine global fixed-endpoint
`C¹` competitor inequality.  The returned curve now also agrees on `[0,b]`
with the totalized maximal `lRegCurve` for its normalized initial tangent.
It additionally exports `b ∈ lRegDomain S T x Z`, so raw-time consumers do not
need to reconstruct maximal-domain membership from the open certificate.

## Route

- Consume `exists_lRegMinC1` directly so that its finite chart-`H¹` realization
  remains available.
- Use that same realization with `lMinCurve_c1` and `lMinCurve_reg` to obtain
  closed-interval `C¹` regularity and the full interior regularized equation.
- Use `exists_lRegExtOn` to replace the curve only outside `[0,b]`, making total
  endpoint derivatives honest and retaining an open solution certificate.
- Transfer the action through `lRegAction_congr`, since the extended curve and
  the direct-method minimizer agree on the closed interval.
- Set `Z = 2⁻¹ • lVelocity alpha 0`, so the normalization
  `lVelocity alpha 0 = 2 • Z` is an algebraic identity.
- Apply `lRegCurve_eqIcc` to the open certificate, identifying the attained
  minimizer with the canonical maximal solution rather than leaving a separate
  ODE witness.

## Verification

Focused verification and the exported-module refresh passed without warnings.

## Project position

This regularized packaging and its maximal-curve identification are complete
(100%).  The compact raw `exists_lMinimizer` is also complete downstream;
`redVolume_anti` remains 0%, P2 remains below 1%, and the whole Poincaré
program remains approximately 3--5%.
