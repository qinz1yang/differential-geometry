# G8 log

- 2026-09-26: new file `Perelman/Noncollapsing/VolumeDistortion.lean` (81 lines, not wired in root aggregate).
  - `riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le`: bound on measurable `U` over `Icc a b`,
    any `A ⊆ U` (no measurability), `s t ∈ Icc a b`:
    `vol_s A ≤ ofReal (exp (n^3/ρ^2 * |s - t|)) * vol_t A`. Symmetric in `s, t`.
  - `riemannianVolumeMeasure_le_exp_cube_mul_of_parabolic_rmNormSq_le`: window `Icc (T - ρ^2) T`,
    constant `exp (n^3)` (`C_V = 27` for `n = 3`).
  - Suppliers: `inner_le_exp_mul_inner_of_rmNormSq_le` (ForwardTransfer),
    `Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le`, `toMeasurable`.
  - No completeness. Compiles clean with `linter.mathlibStandardSet`; axioms propext, Classical.choice, Quot.sound.
