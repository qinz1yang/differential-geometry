# Contractions

## 2026-07-12 branch-alignment compatibility

`rm13_oneForm_apply_eq_sum_inv_flat` no longer needed the old explicit
`ContinuousMultilinearMap.smul_apply` rewrite after `map_smul`; the evaluation is definitional in
the current tensor API and is closed by `rfl`. Focused verification and targeted build passed.
This theorem and its dedicated machinery are complete (100%); this is compatibility maintenance,
not new Hamilton theorem progress.
