# L4 fill log (DESIGN_C3B brick L4: perturbation of a strict windowed witness)

## 2026-09-26 entry 1

File: `Perelman/CanonicalNeighborhood/WindowedWitnessPerturbation.lean` (1113 lines, new, not
registered in the root aggregate, no other file edited, no git writes, no `lake build`).
Single import `...CanonicalNeighborhood.WitnessStrictStability`; the L2/L3 file is not needed.

Headline (sequence form, as DESIGN_C3B §4 L4):
`WindowedModelWitness.eventually_strict_of_tendsto_flows` — flows `S n`, `S₀` on the same `D`,
strict witness `W` for `S₀` at `(x,t)`, `hwindow : Icc (t - (eps*R₀)⁻¹) t ⊆ D.regular`,
closeness `hconv : ∀ K compact, ∀ p e, 0<e → ∀ᶠ n, ∀ τ ∈ D.carrier,
metricDerivNormSupOn K p (S n τ) (S₀ τ) R < e`, `x' n → x`, and
`hscalar : Tendsto (fun n => (S n).scalar t (x' n)) atTop (𝓝 (S₀.scalar t x))`.
Conclusion: eventually the window of `S n` at `(x' n, t)` is regular and there is a strict
witness `W'` for `S n` at `(x' n, t)` with the same embedding (model = W's model renormalized at
`W.embedding.symm (x' n)`), plus orientation transfer from `W` to `W'`.
Corollaries: `WindowedModelWitness.eventually_of_tendsto_flows` (design's exact pointwise
`metricDerivNorm` hypothesis, `Nonempty` conclusion), `orientedWitness_eventually_of_tendsto_flows`.

Isolated hypothesis: `hscalar` (scalar convergence at the moving point). Mathematically implied by
`hconv` (order 2) plus continuity of `S₀.scalar`; no library lemma turns `metricDerivNormSupOn`
closeness into scalar closeness, so it is an explicit input.

Route: pull the flows back to the model open set `U` (cutoff region) through
`toOpensDiffeo`; `uniform_ordinary_metric_jets_of_metric_convergence_on_closed_interval` there
gives uniform chart jets of the time towers (`uniform_pullback_time_tower_chart_jets_...`);
a perturbed version of `eventually_strict_weighted_error_norm_on_scaled_ball` absorbs them;
`exists_recentered_strict_of_flow_time_towers` (= the existing recentered construction with the
target flow freed) builds `W'`. `source_capture` is re-derived from the new comparison
(`exists_source_capture_reserve`), `buffered_ball`/`base_map` are topological on the same
embedding.

Duplication debt (follow-up, needs edits outside this file): four private helpers are copies of
private lemmas in `WitnessMovingNorm`, `WitnessStrictNorm`, `UniformTensorNorm`,
`WitnessNormalizedNormConvergence`; the existing `eventually_strict_weighted_error_norm_on_scaled_ball`
and `exists_recentered_strict_of_time_towers` are special cases of the new perturbed lemmas.

Compile: `LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
-Dweak.linter.mathlibStandardSet=true` in place: no output. `#lint` (scratch copy): 0 errors, 14
linters. Axioms (scratch copy, all 8 public theorems): `propext`, `Classical.choice`,
`Quot.sound`. Public names grep-unique.
