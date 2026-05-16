# Field notes

## 2026-05-10 warning cleanup

- Worked: replaced two `show` tactic uses with `change` where the tactic was
  intentionally changing the goal shape.
- Failed: no proof obstruction appeared.
- Remaining risk: none from this pass; the focused locked check of
  `DifferentialGeometry/Tensor/Multilinear/Field.lean` passed.
