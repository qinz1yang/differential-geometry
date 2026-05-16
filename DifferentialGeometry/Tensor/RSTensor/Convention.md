# Convention

## Goal

Give high-level curvature and Ricci-flow proofs a small import that fixes the
realized tensor slot conventions without exposing representation internals.

## Worked

- Added named component lemmas for common arities:
  `component11_apply`, `component13_apply`, `component02_apply`, and
  `component04_apply`.
- Added convention lemmas documenting that `componentRS` means
  `T(e^upper)(e_lower)`, that `contract_trace` contracts first upper with first
  lower, and that `contract_contravariant` prepends the contracted covector in
  the model formula.

## Failed

- No proof obstruction yet.

## Next

- High-level files should import this convention layer instead of unfolding
  `basisTensor0S` or the Hom representation directly.
