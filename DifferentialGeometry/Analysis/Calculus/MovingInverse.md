# MovingInverse

## 2026-07-16 compact target inverse convergence

`OpenPartialHomeomorph.exists_symm_cInf` extends the moving-inverse API from a
ball around the origin to a neighborhood of an arbitrary compact subset of the
limiting target.  It derives a common open target neighborhood, compact
closure, eventual membership in every stage target, stage-inverse maps into
the fixed source domain, and exact inverse `C∞` convergence.

The proof reuses the checked compact-root tube and identifies its selected
roots with the partial-homeomorphism inverses by stage source injectivity.  It
adds no endpoint radius or stage-family stay assumption.  Focused verification
passed.  This is generic analysis machinery; the HCG compact-diagonal wrapper,
the `StepB1RawInput` producer, and textbook B1 remain separate downstream
theorems, with the latter two still at 0%.
