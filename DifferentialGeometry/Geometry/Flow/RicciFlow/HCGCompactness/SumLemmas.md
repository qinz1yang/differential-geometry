# SumLemmas.lean notes

## Lemma 4.5 algebra layer

This file is geometry-free.  It contains the finite-sum estimates for MSM135
Lemma 4.5:

- `sum_range_le_sum_range`;
- `sum_shift_le_full`;
- `single_le_sum_range`;
- `oneStep_partial_to_full`;
- `oneStep_from_leibniz`;
- `oneStep_from_antidiagonal`;
- `main_step_algebra`;
- `main_step_to_lemma45Const`;
- `main_step_to_lemma45Const_of_partials`.

The new scalar endpoint `oneStep_from_leibniz` is meant to consume a future
tensor Leibniz estimate and convert it into the `oneStepConst` coefficient.
The antidiagonal variant matches the natural form of an iterated Leibniz
formula indexed by pairs `(a,b)` with `a + b = k`, avoiding subtraction in the
future tensor-calculus theorem.  Verification passed.

The remaining frontier is not arithmetic.  It is the tensor-calculus producer:
an iterated `H`-covariant Leibniz estimate for repeated derivatives of the
connection-difference action.
