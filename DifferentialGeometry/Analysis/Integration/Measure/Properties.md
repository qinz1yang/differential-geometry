# Properties.lean — B5a additions (deliverable L4)

Only the two additive public lemmas below were added (git diff = 34 insertions / 0
deletions; the private `pou_term_le_chartLocalMeasure` and all existing statements are
untouched). This note covers only the B5a additions, not the whole file.

## Results

Both `[T2Space M] [SigmaCompactSpace M]`, `g : SmoothRiemannianMetric I M`,
`hS : MeasurableSet S`, namespace `DifferentialGeometry.Integral.Measure`:

- `vol_le_tsum_supp` (PRIMARY, useful):
    `riemannianVolumeMeasure g S ≤ ∑' α : M, chartLocalMeasure g α (S ∩ tsupport (chartAtlasPOU I M α))`
- `vol_le_tsum_chart` (the brick's literal target, documented coarsening):
    `riemannianVolumeMeasure g S ≤ ∑' α : M, chartLocalMeasure g α S`

Route: `riemannianVolumeMeasure_def` → `riemannianMeasure_def` → `Measure.sum_apply _ hS`
→ per-summand `pou_term_le_chartLocalMeasure` (private, in-file) → `ENNReal.tsum_le_tsum`.
`vol_le_tsum_chart` = `vol_le_tsum_supp` composed with `measure_mono inter_subset_left`.

## KEY FINDING — the brick's literal target is generically vacuous

`chartLocalMeasure g α` is the pushforward supported on `(chartAt α).source`, so for a
FIXED positive-measure `S` the sum `∑' α : M, chartLocalMeasure g α S` has uncountably many
positive summands (every chart source that meets `S`) ⇒ generically `= ⊤`. So the literal
`vol_le_tsum_chart` is usually vacuous.

The genuinely useful bound keeps the partition-of-unity support restriction: the summand
`chartLocalMeasure g α (S ∩ tsupport (ρ α))` vanishes whenever `support (ρ α) = ∅`, i.e.
off the **countable** set `{α | (support (ρ α)).Nonempty}` (`countable_nonempty_support_of_pou`,
Invariance.lean:922). Hence `vol_le_tsum_supp` is the finite (up to bounded overcounting)
form L5 should consume. Both are shipped; `vol_le_tsum_chart` carries a docstring warning.

This is the same class of catch as the orchestrator's B2 σ-mass review: a plausibly-stated
upper bound that is silently trivial on the model case.

## modelHaar pullback for L5 — NOT re-added

The per-chart `chartLocalMeasure g α S = ∫⁻ … ∂ modelHaar` shape L5 needs is already public
and usable: `chartLocalMeasure_setLintegral_indicator` (Invariance.lean:573, take
`F := fun _ => 1`) and `chartLocalMeasure_lintegral` (Invariance.lean:472). No thin adapter
added (brick: only add if the existing shapes don't directly give it).

## Verification

Focused check + targeted module build PASSED. Additions-only, sorry-free, no new axioms.
The `[Module.Finite ℝ E]` unusedSectionVars warning is pre-existing and file-wide (it cannot
be `omit`ed — the variable is referenced by the section instance graph, "cannot omit
referenced section variable"); my two lemmas carry it exactly like every other theorem here.
