# Basic notes

## 2026-05-10 warning cleanup

- Worked: removed stale simp arguments in the coordinate Christoffel bridge and
  replaced an unnecessary `simpa` with `simp`.
- Failed: replacing `simp [Bundle.Trivialization.basisAt]` with the linter's
  suggested `simp only` left an unsolved basis-coordinate goal. The final edit
  keeps the original simplification and disables only the flexible-tactic linter
  for that theorem.
- Remaining risk: none from this pass; the focused locked check of
  `DifferentialGeometry/Coordinates/NablaComponents/Basic.lean` passed.

## 2026-05-10 coordinate abstraction

- Worked: this file now consumes `Coordinates.ConnectionCoefficients` instead
  of owning the general coordinate-frame local-frame and connection-coefficient
  bridge declarations.
- Worked: the tensor-model derivative and `nabla0S_coordFrame_slots` layer
  stayed here, which keeps the split by functional theorem family intact.
- Verification passed.
## 2026-05-10 scalar genericity

- Worked: generalized `coordDeriv0SAt`, `modelDeriv0SAt`,
  `ModelDerivEqCoordDeriv0SAt`, and the coordinate-frame `nabla0SFun`
  component formulas from `Real` to `ð•œ`.
- Worked: all coordinate-index arguments are now explicitly
  `CoordinateIdx (ð•œ := ð•œ) E`, which avoids metavariable-stuck
  `FiniteDimensional ?m E` goals in generic theorem statements.
## 2026-05-11: Smooth coordinate derivative layer

- Lowered `modelDeriv0SAt`, `ModelDerivEqCoordDeriv0SAt`, `modelDeriv_eq_coordDeriv0SAt`, and the generic `nabla0S_coordFrame_slots` theorem family from analytic/top regularity to smooth regularity.
- Verification passed.

## 2026-05-12: Rank-generic model component factory

- Added `nabla0S_model_coordFrame_slots`, the generic `(0,s)` model-component
  formula for `nabla0SFun`.
- `nabla0S_coordFrame_slots` now delegates to this model formula and only
  rewrites the derivative term through the supplied derivative bridge.
- Verification passed.
