# OPUS_FILL_LOG_L10C (jet hypothesis of `exists_slice_bounds_at_slab_start` on the post-event slice)

## 2026-09-26 entry 1 (start)

Read: AGENTS.md, L10B log and its two files, C3B2 log (class-prefixed statement), consult F digest
item 6, `CanonicalWitness`/`SpatialCanonicalWitness`/`WindowedModelWitness`, `StaticCapWitness`,
`PresentedStaticCap`, `GeometricCutoffRecord`, `hasCanonicalWindow`, `EventCapCapture`,
`MetricCutCapScalarLower.capRegion`, `CapWindowDerivativeTransfer` (idiom: standard-cap closeness
=> jets and scalar lower bound at the neck scale), `StandardCurvatureComparison`,
`StandardActionComparison`, `InitialScalarDerivativeBounds`.
Finding (supplier (1)): `CanonicalWitness` carries only `rm_bound` (order 0), `gradient` and
`time_derivative`; no tree lemma produces `|∇ᵏRm|² ≤ K R^(k+2)` (k = 1, 2) from the class's
induction data (`CanonicalBefore/On`, `EventSlabs*`). The `curvDerivNormSq` users in
`StrongNeckCanonical`/`LocalCapCanonicalWitness`/`CompactPositiveCanonical` CONSUME jets.
Plan: file A `StaticCapCurvatureJets.lean` (caps: closeness at order >= 4 => normalized jets and
`R >= c Q`), file B `SlabStartCurvatureJets.lean` (split of the post-event slice into regular
crossings and caps, `k = 0` vacuous, headline conditional on the old slab's near-end jets clause).
Compile: file A in place; file B in `scratchpad/l10c` on top of the L10b scratch oleans.

## 2026-09-26 entry 2 (owner directive received: deliver the unconditional statement)

Route change. The jets route for the retained core is circular in the constants: jets of the old
slab at order 2 would come from Shi at scale with a window set by `Ctime` (or by the witness
constant `C2`, or by `κ`), and all of these are quantified after `Cs`, so `Cs ≥ C(K₁(Ctime))`
cannot be arranged. Retained core instead uses derivative matching across the event (consult F
item 6): `∂ₜ⁺R_new(a,y) = (ΔR + 2|Ric|²)(g_a)(y) = (ΔR + 2|Ric|²)(g_term)(p) =
lim_{t→a⁻} ∂ₜR_old(t,p)`, bounded by the old slab's `DerivativeBoundBefore Ctime qcan` (same
constant, from `EventSlabsDerivative`). Caps keep the jets route (constant from the standard cap).

## 2026-09-26 entry 3 (delivered; failures first)

### Not done
- No wiring: the files are unregistered in `DifferentialGeometry.lean`, and nothing else is edited.
- The earlier conditional draft `SlabStartCurvatureJets.lean` (it needed an old-slab jets clause)
  was deleted. It is superseded.
- The short name `exists_slice_bounds_at_slab_start` now exists twice, in different namespaces:
  L10b's `OrientedThreeStage.IncomingSlab.…` (the jets→slice lemma) and the new
  `RetainedCoreHistory.…` headline. Full names are unique. Renaming one of them is optional.

### Proved (all unconditional; axioms propext, Classical.choice, Quot.sound)
Headline `RetainedCoreHistory.exists_slice_bounds_at_slab_start (P₀) (g₀)` is in
`Surgery/Topology/SlabStartDerivativeBounds.lean`. It is verbatim the C3B2 `hslice` statement,
with constants `Cs = n⁶√K + 2n⁴K` (`K = B / min(c,1)⁴`, from the standard cap only),
`Rs = transitionEnd + 1`, `qs = Q₀` (the initial scalar bound through `InitialIdentification`),
`ms = 4`, `εs = ε₀` (the cap closeness), and `δs = ρs = 1`. The proof splits on `k`:
- `k = 0`: vacuous, since `R < Q₀ ≤ qcan`.
- `k = j+1`, a point in `capRegion`: jets via the window closeness, then L10b's pointwise
  jets→derivative lemma.
- `k = j+1`, otherwise: a regular crossing (`exists_regularCrossing_of_not_mem_capRegion`), then
  derivative matching with `EventSlabsDerivative` at `j`.
- `hreg`: L10b's `continuousWithinAt_derivWithin_Ici_scalar_at_start`.
Plug-in check (scratch): `capWindowContinuation_of_slab_start_bounds P₀ g₀
(RetainedCoreHistory.exists_slice_bounds_at_slab_start P₀ g₀) : CapWindowContinuation P₀ g₀`
elaborates. Its axioms are propext, Classical.choice, Quot.sound.

Files (new, no header or comments, lines ≤ 100):
- `StaticCapCurvatureJets.lean` (147 lines): `isCompact_standardCapWindow_norm_le`, and in
  `PresentedStaticCap` the lemmas `metricDerivNorm_window_lt`, `window_isLocalDiffeomorph`,
  `curvDerivNormSq_output_window`, `metricScalarAt_output_window`. Main result:
  `exists_presentedStaticCap_window_curvature_bounds`: `∃ ε₀ c B`, for window closeness `≤ ε₀` at
  order `≥ 4` and `‖x‖ < D`, we get `c·Q ≤ R(output, window x)` and
  `|∇ⁱRm|² ≤ B·Q^(i+2)` for `i ≤ 2`.
- `ScalarLaplacianRicciTerms.lean` (257 lines, namespace `Geometry.Curvature`, promotion
  candidate). It defines `scalarEvolutionRate g x := Δ_g R_g + 2|Ric_g|²` and proves:
  - the chart-sum formulas;
  - `continuousWithinAt_scalarEvolutionRate_of_chartGramFamilySmoothWithinOn`;
  - `scalarEvolutionRate_eq_of_local_isometry`;
  - `scalarEvolutionRate_restrictOpen`.
- `CrossingScalarEvolutionRate.lean` (133 lines):
  - `IncomingSlab.hasDerivAt_scalar_scalarEvolutionRate`;
  - `IncomingSlab.derivWithin_Ici_scalar_at_start_eq_scalarEvolutionRate`;
  - `IncomingSlab.TerminalLimitMetric.abs_scalarEvolutionRate_le` (the old-side limit);
  - `MetricCutCapEvent.RegularCrossing.scalarEvolutionRate_eq`;
  - `MetricCutCapEvent.abs_derivWithin_Ici_scalar_le_at_slab_start_of_regularCrossing`.
- `SlabStartDerivativeBounds.lean` (137 lines): `exists_scalar_lt_at_initial_slab_start`,
  `exists_abs_derivWithin_Ici_scalar_le_at_cap_slab_start`, and the headline.

Compile (read-only, `LEAN_NUM_THREADS=2`, `-DmaxSynthPendingDepth=3
-Dweak.linter.mathlibStandardSet=true`):
- The first two files compiled in place with `lake env lean`, with no output.
- The last two import the uncommitted L10b files, so they were compiled with the scratch-module
  pattern in `scratchpad/l10c` (`build.sh`): `L10cScratch.{Caps,Terms,Rate,Slice}` on top of
  `L10bScratch.{Start,Crossing}`. The copies differ only in their import lines. No output.
- Leaf check: `scratchpad/l10c/buildc.sh`, modules `L10cCheck.*` on top of `C3b2Scratch.Leaf`.
- `#lint`, 14 linters: 0 errors except `docBlame` on the def (inapplicable per AGENTS.md).
- Public names are grep-unique.
- No `lake build`, no git writes.

Note (end of lane): the L10/L10b/C3b2 inputs were committed in 0798da941 during the lane. Their
sources match the scratch copies I compiled against (checked with `diff`; only import lines differ),
so the scratch results carry over. There is an uncommitted edit in
`CanonicalNeighborhoodContinuationLeaves.lean` by another lane. It touches only
`CrossingContinuation`, which these files do not use.
