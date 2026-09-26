# L1 — standard-solution compactness (2026-09-26)

New file `Perelman/StandardSolution/StandardFamilyCompactness.lean`.

- No uniqueness of the standard solution exists in the tree (grep `unique` over
  `StandardSolution/`): the family is not trivialized; a genuine subsequence is extracted.
- The compactness already exists: `exists_standard_solution_subsequence_on_shorter_interval`
  (`SequentialCompactness.lean:15`, on E3, `Ico 0 T`, `ofReal T < uniformStandardLifetime`),
  with `uniformStandardLifetime_eq_one` (`StandardLifetime.lean`). L1 is a corollary at
  `T := (max Θ 0 + 1)/2`; the design's route via `InitialMetricLimit` is unnecessary.
- Delivered: `StandardSolution.exists_subseq_tendsto_on_compact` (E3, compact K, `Icc 0 Θ`,
  Θ < 1), `…_restrictOpen` (every open U, one subsequence), `StandardSolution.exists_subseq_tendsto`
  (design shape; ∀ D : ℝ instead of n : ℕ, no `0 ≤ Θ` needed).
