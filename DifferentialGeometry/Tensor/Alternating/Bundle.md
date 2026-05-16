# Bundle notes

## 2026-05-10 warning cleanup

- Worked: removed the unused `Fintype` section-variable warning on `continuousAlternatingMapCoordChange_apply` with a local `omit` wrapper.
- Failed: placing `omit ... in` after the doc comment caused a parse error. The correct form wraps the doc comment and declaration together.
- Remaining risk: none from this pass; the focused locked check of `DifferentialGeometry/Tensor/Alternating/Bundle.lean` passed.
