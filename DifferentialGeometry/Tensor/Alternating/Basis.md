# Basis notes

## 2026-05-10 warning cleanup

- Worked: removed the unused `CompleteSpace` and `FiniteDimensional` section-variable warnings on the two elementary-covector basis theorems with local `omit` wrappers.
- Failed: the first placement put `omit ... in` between the doc comment and theorem, which Lean parses as an invalid command. The wrapper has to sit before the doc comment so it wraps the whole declaration.
- Remaining risk: none from this pass; the focused locked check of `DifferentialGeometry/Tensor/Alternating/Basis.lean` passed.
