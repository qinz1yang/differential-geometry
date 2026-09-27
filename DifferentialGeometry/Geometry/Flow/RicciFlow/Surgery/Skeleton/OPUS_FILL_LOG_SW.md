# OPUS_FILL_LOG_SW — standard solution's own canonical witnesses (2026-09-26)

- Survey: clause 2 (strong, age-restricted) already proved:
  `PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_age`
  (`Perelman/StandardSolution/CanonicalWitnessPositiveAge.lean:66`), condition `τmin ≤ t·R(t,x)`, `t < 1`.
  The form "`t ≥ τ₀`" is vacuous there (`τmin ≥ 1`, `R ≥ 1` by `one_le_scalar`, `t < 1`).
- Clause 1 (spatial, all points of `[0, Θ]`): old part (`τmin ≤ t·R`) by projection; young part
  (`t·R < τmin`: far necks at positive time, tip caps at all `t ≤ Θ`) not in the tree.
- New file `Perelman/StandardSolution/StandardSpatialCanonical.lean` (not wired): spatial
  `enlarge_constants`, old-region spatial clause, young clause as named Prop
  `StandardSolution.YoungSpatiallyCanonical`, assembly to all of `[0, Θ]`.
- Compiled read-only (`LEAN_NUM_THREADS=2 lake env lean`, after the running build produced the missing
  oleans): no diagnostics. Axioms (scratch copy, deleted): propext, Classical.choice, Quot.sound.
  `#lint`: only docBlame (excluded). Lines ≤ 100.
- Open: `YoungSpatiallyCanonical` (points with `t·R < τmin`, `t ≤ Θ`): needs (a) uniform far necks
  at positive time from `exists_standard_cylinder_metric_subsequence_at_tendsto_time` → SpatialNeck,
  (b) tip `SpatialLocalCap` at every `t ≤ Θ` (tree has only the `t ≤ η` frontier construction),
  (c) witness fields (ball sandwich, volume, gradient) uniform over all `StandardSolution`s.
