# OPUS fill log SP1: strong-neck production bricks (2026-09-26)

Worker lane SP1. Scope: `DESIGN_STRONG_INTERFACE.md` §1 predicates (I1) + one-line lemmas + cover
lemma; brick P1 (old points); S1′ (standard-solution full/truncated dichotomy); S2e (depth deficit).
New files only. Read-only compiles (`LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
-Dweak.linter.mathlibStandardSet=true`). No git writes, no lake build, no root-aggregate edit.

## Progress

- 00:00 read AGENTS.md (pc3 variant: no header, no module docstring, zero comments) and the design.
  Grep: `HistoryStrongNeck`, `StronglyCanonical*`, `TruncatedNeck` unused in the tree.
- +0:30 predicates probe: §1 (I1) text elaborates verbatim (no extra instance needed); the
  one-line lemmas and the cover lemma prove as in the design.
- +0:45 new generic brick `StrongNeck.restrictOpen` (`Perelman/CanonicalNeighborhood/StrongNeckRestriction.lean`,
  mirrors `SpatialNeck.restrictOpen`; exact, no accuracy loss; hypothesis: the restricted solution's
  metric is `restrictOpen` at every time). Compiles clean.
- +0:50 lead message: review H17 (`Surgery/consult/H17-a-lite-strong-necks-review-digest.md`) —
  S1′ must require `t > 0` (design text allowed `t = 0` with depth in `(0,1]`: definite error);
  S2e must be restated as a survival-or-cap-witness dichotomy with `O(δ)` uniform in the later `p₀`;
  if an input is missing, record exactly which and stop at the strongest provable statement.
  P1 and the predicate file unchanged.
- +1:10 DONE (1)+(P1)+(P0b): `Surgery/Topology/HistoryStrongNeck.lean` compiles (scratch import of
  StrongNeckRestriction): the §1 (I1) predicates verbatim; `spatiallyCanonicalBefore`,
  `of_threshold_le`, `stronglyCanonicalBefore_of_where_cover` (design text), P1
  `stronglyCanonicalWhere_of_canonicalBefore` (design statement verbatim), P0 helpers
  `ObservedHistory.mem_backwardSurvivorDomain_self`, `ObservedHistory.historyStrongNeck_of_strongNeck`
  (a `StrongNeck` of the current slab gives `HistoryStrongNeck` with `first := k`, exact window
  `R⁻¹`), and P0b `StronglyCanonicalWhere.mono_constants`. Axioms: propext, Classical.choice,
  Quot.sound. `#lint`: only docBlame (excluded).
  DEVIATION P0b: dropped the design's `hC1p : 1 ≤ C1`, `hC2p : 1 ≤ C2` (unused; `enlargeConstants`
  needs neither; keeping them fails `unusedArguments`). Strictly weaker hypotheses.
- +1:30 `TruncatedNeck` (`Perelman/CanonicalNeighborhood/TruncatedNeck.lean`): the structure exactly as
  §1 describes (StrongNeck + `depth ∈ (0,1]`, window `Icc (t − depth·R⁻¹) t`, comparison on
  `Icc (−depth) 0`), with `TruncatedNeck.mono` (ε-monotone) and `TruncatedNeck.restrictOpen`
  (exact, for the S2 splice into survivor domains). Compiles; axioms propext/choice/Quot.sound;
  `#lint` only docBlame.
- +1:35 S1′ statement elaborated with the H17 fix (`t ∈ Ioc 0 Θ` instead of `Icc 0 Θ`), otherwise
  verbatim (probe, sorry body). NOT proved — see findings.

## Findings (failures first)

### S1′ is not an 800–1500-line brick: its analytic core is missing from the library
Both branches need a spacetime `MetricComparisonOn` WITH TIME JETS on windows that reach the
standard solution's INITIAL time 0:
- truncated branch (`tR < 1`): window `[0, t]`, i.e. `Icc (−tR) 0` touches τ = 0 by definition;
- full branch at `tR ≈ 1`: window start `t − R⁻¹ → 0`, and in any compactness argument `t_n → 0`
  or `t_n R_n → 1` forces uniform jet control near τ = 0.
Every producer of time-jet comparisons in the tree needs interior slack `a < c` BEFORE the window:
`eventually_metricComparisonOn_of_local_flow_convergence` (CompactTimeComparison:23),
`exists_metric_time_jets_extension_on_compact` (OpenTimeJetExtension:28),
`exists_closedWindow_metric_time_fields` (ClosedWindowMetricFields:134),
`exists_ordinary_metric_time_jets_on_closed_interval` and the jet polynomial formula (TimeJets:235,263),
`exists_mixed_curvature_fields_on_closed_interval` (TimeJetFields:138),
`uniform_metric_time_jets_on_compact_closedWindow` (UniformOrdinaryMetricJets:30),
`BumpMetricConvergence.eventually_metric_comparison` (Fields/Open/MetricComparison:199).
Only TERMINAL-endpoint versions exist (`mixedCurvature_polynomial_terminal_of_regular_Icc`,
`iteratedMetricTimeDerivWithin_eq_of_terminal_tower_Icc`, `solution_*_continuousWithinAt_terminal`).
The standard-solution far-region results are SPATIAL only (`exists_far_radial_spatialNeck`,
`exists_standard_cylinder_closed_limit` gives spatial `derivNormSupOn` on `Icc 0 τ` + Lipschitz;
`standard_closed_source_first_time_jet_converges_on_compacts` gives only the first time jet, 0-order).
What the tree does have that makes it feasible: `PartialStandardSolution.smooth` (joint C^∞ on
`[0,L) × E3`), `equation` within `Ici 0` AT τ = 0, closed curvature-derivative bounds
(`uniformStandardLifetime_curvature_derivative_bounds_closed`, `…first_time_curvature_bounds_closed`),
closed Gram smoothness of the cylinder limit on `Icc 0 τ`, and its identification with the shrinking
cylinder (`standard_cylinder_closed_limit_eq_shrinking`).
Needed layer (my estimate): INITIAL-endpoint mirrors of the terminal chain (tower lemma, curvature-jet
polynomial continuity, mixed-curvature polynomial at the initial point, closed-window metric jet
fields/polynomial formula, local-flow-convergence comparison with `a = c`) ≈ 1500–2500 lines; then
S1′ proper (compactness far out, cylinder model neck with scalar-mismatch `R(1−t) ≠ 1` handled in jet 0
only, transport to strong/truncated necks, tube avoidance `‖·‖ > Dcore`, near points via the private
`exists_tip_spatialCanonicalWitness` at radius `max D D_far`) ≈ 1000–1500. Total 2.5–4k. The same
initial-endpoint layer is needed by S2 (post-gluing window starts at the gluing time; the
`CapWindowStandardComparison` output is spatial-only on `Icc 0 (scale·(t−T))`). Not started: needs the
lead's go-ahead / split (it is shared infrastructure, better its own lane).

### S2e: a class input is missing (H17 confirmed, made precise)
- Where the deficit is real: at OLD-material points of the incoming neck at times `t ∈ [T, T+σ]`
  (`T = H.time j.succ`), `R(y,t)⁻¹` can exceed `r² + (t−T)` by `O(η + εcap)·r²` (η < δ the record's
  `parabolic_closeness`, εcap the model accuracy). This constant IS uniform in the later `p₀` if it is
  derived geometrically from the two closeness statements at the same point and time; it is NOT
  obtainable from the recentering bound `|S/N − 1| ≤ Λδ` (Λ = `p₀.recenterConstant`, only
  `Λ·δbound ≤ 1/2`, i.e. a factor-2 mismatch, deficit up to r²).
- What no class/record field supplies on the deficit interval `[t − R⁻¹, T − r²]`:
  (i) existence of history there beyond `IncomingBackwardNeck.left_nonneg : 0 ≤ T − r²` (only the
  class's derivative bound + initial normalisation can push `T − r²` away from 0, and only with a
  `ρmax` depending on g₀);
  (ii) survival of the whole ε₁-tube across events in that interval — `stageChart`/`crossing` cover
  only events with `T − r² < H.time j.succ`; an event at `T' ∈ (T − r²(1+Cδ), T − r²]` can glue new
  material into the tube;
  (iii) the higher-order comparison (`a + 2b ≤ ⌈ε₁⁻¹⌉`, time jets) there — curvature and
  time-Lipschitz bounds give C⁰ scalar control only, never the jets.
- The cap-witness branch of the H17 dichotomy is also not supplied: at a point deep in a long old
  neck whose backward tube meets an earlier gluing at T', no cap core lies within `C1h/√R` in general.
- Exact missing input (minimal form): a record field certifying the incoming neck on normalized
  times `[−(1+c), 0]` for a fixed `c > 0` (or `IncomingBackwardNeck` at a radius `r' = r√(1+c)` with
  its model cylinder normalised at `R = 1/(1+c)`), including `crossing` for events after
  `T − r²(1+c)`. With it S2e becomes the pure interval arithmetic `R⁻¹ − (t−T) ≤ r²(1 + C(η+εcap))`,
  `C(η+εcap) ≤ c`. Without it, no S2e statement is provable; I stopped here as instructed.
  Strongest provable piece not formalised (it would be the arithmetic inequality alone, which is
  vacuous without (i)–(iii)).

## Deliverables
| File (new) | Lines | Content | Compile |
|---|---|---|---|
| `Surgery/Topology/HistoryStrongNeck.lean` | 160 | §1 (I1) predicates verbatim; one-line lemmas; cover lemma; P1; P0 helpers; P0b | clean (scratch import) |
| `Perelman/CanonicalNeighborhood/StrongNeckRestriction.lean` | 91 | `StrongNeck.restrictOpen` | clean |
| `Perelman/CanonicalNeighborhood/TruncatedNeck.lean` | 132 | `TruncatedNeck`, `.mono`, `.restrictOpen` | clean (scratch import) |
All: axioms `propext, Classical.choice, Quot.sound`; `#lint` only docBlame; no comments/docstrings; long
lines are imports only; new names unique. Not in the root aggregate. Acceptance order:
StrongNeckRestriction → TruncatedNeck → HistoryStrongNeck (all three depend only on committed modules
besides each other). No `open private`, no deferred merges.
Deviations: P0b drops the unused `1 ≤ C1`, `1 ≤ C2`; S1′ statement uses `t ∈ Ioc 0 Θ` (H17).

## Round 2 (lead decision: quarter-strong necks, S2e dropped, S1′ via the cap-window chain)

### New predicate (for review)
`HistoryStrongNeck k G eps y t` now certifies depth `θ₀·R(y,t)⁻¹` with `θ₀ = 1/4`: the window
conjunct is `H.time first ≤ t - 1 / 4 * (G.flow.scalar t y)⁻¹`, and the last conjunct is
`Nonempty (TruncatedNeck (flow of gflow on closedOpen (H.time first) s) eps (1 / 4) z t)`, i.e. the
cylinder comparison of `rescaledMetric` at `(z,t)` on normalized times `Icc (−1/4) 0` (window
`Icc (t − R⁻¹/4) t`), order `⌈eps⁻¹⌉`, accuracy `eps`. All other conjuncts (survivor domain, slab
equalities, terminal equality, `IsSolutionOn`) unchanged. `StronglyCanonical*`, the one-line lemmas,
the cover lemma and mono-constants are unchanged and re-compile.

### P1 re-verified
New generic bricks in `Perelman/CanonicalNeighborhood/TruncatedNeck.lean`:
- `StrongNeck.comparison_jet_differentiableWithinAt_of_lt_one`: for `d < 1`, the comparison jets of a
  strong neck of an `IsSolutionOn` flow are differentiable within `Icc (−1) 0` at every `s ∈ Icc (−d) 0`,
  given only `Ioo (t − R⁻¹) t ⊆ D.regular` (the depth margin replaces the buffer BEFORE the window that
  the private `comparison_jet_differentiableWithinAt_of_buffer`, CanonicalWitnessComparisonTransport:25,
  needs — that buffer does not exist when `t − R⁻¹ = H.time k`);
- `TruncatedNeck.ofStrongNeck` (`restrictTimes` to `Icc (−depth) 0`).
`historyStrongNeck_of_strongNeck` now goes StrongNeck → quarter TruncatedNeck → `restrictOpen`;
P1 `stronglyCanonicalWhere_of_canonicalBefore` statement unchanged, proof unchanged. Both compile,
axioms propext/choice/Quot.sound, `#lint` docBlame only.

### S2e dropped — justification (normalizations from the record definitions)
- Incoming neck: `backward α : IncomingBackwardNeck H i (neck α) r` with `r = nominalRadius ⟨α⟩`
  (GeometricCutoff.lean:226) and `scale_eq : (neck α).scale = (r ^ 2)⁻¹` (:221): `N = r⁻²`, certified
  window `[T − r², T]`, `T = H.time i.succ`.
- Cap scale `λ = ((records j).static b).neck.scale`; `recenter_scale_comparison` (:253) with
  `Λ·δ ≤ 1/2` gives `N/2 ≤ λ` (the `hS` step inside `inv_two_mul_sq_lt_static_scale`,
  CanonicalNeighborhoodContinuationLeaves.lean:88): `λ⁻¹ ≤ 2r²`.
- Young cap-window point at `t = T + τ/λ`: `R(y,t) ≥ λ·R_Q(τ)/2` (order-≤2 closeness of
  `CapWindowStandardComparison` with η small) and `R_Q ≥ 1` (`one_le_scalar`), so
  `θ₀/R ≤ 2θ₀/λ ≤ 4θ₀r²`. Hence `t − θ₀/R ≥ T + τ/λ − 4θ₀r² ≥ T − r²` iff `θ₀ ≤ 1/4`.
  `θ₀ = 1/4` works exactly (no slack: equality when λ = N/2, R = λR_Q/2, R_Q = 1, τ = 0); the window
  never leaves `[T − r², t]`. No smaller θ₀ is forced.

### S1′ status: NOT proved; exactly what is missing
- With quarter necks the S1′ conclusion becomes: far neck witness ⇒ quarter `TruncatedNeck` of the
  standard solution `Q` when `tR ≥ 1/4`, else a truncated neck of depth `tR` (window `[0,t]`).
  Both need a `MetricComparisonOn` with TIME JETS on windows that start at, or approach, τ = 0.
- The cap-window chain does not supply jets: `CapWindowStandardComparison` (…:20) outputs only
  spatial closeness `metricDerivNorm i … < ε`, `i ≤ N`, at each τ (lines 104, 108) plus closed chart-Gram
  smoothness; `CapWindowDerivativeBounds.exists_derivative_gradient_bounds_of_cap_window_trace` (:153)
  and `CapWindowDerivativeTransfer` (:68, :205) give scalar `∂_t R` / gradient bounds only;
  `WindowPersistence` (:1029, :1168) produces the prepared flow, spatial.
- Every jet-comparison producer needs slack before the window start: CompactTimeComparison.lean:23,
  OpenTimeJetExtension.lean:28, ClosedWindowMetricFields.lean:134, Evolution/Metric/TimeJets.lean:235
  and :263, Evolution/Curvature/TimeJetFields.lean:138; only terminal-endpoint versions exist
  (KappaSolutions/MixedCurvatureTerminal.lean:123).
- Route that avoids a start-of-window layer entirely (recommended; history level, not standard-solution
  level): on the survivor domain the history flow is ONE smooth solution across the gluing time
  (`exists_backwardSurvivor_isSolutionOn`, HistorySurvivorFlow.lean:180), so the quarter window
  `[t − R⁻¹/4, t] ⊆ [T − r², t]` has interior slack `T − r² < t − R⁻¹/4` except in the equality case;
  jets before T come from `IncomingBackwardNeck.parabolic_closeness` (GeometricCutoff.lean:96, it
  carries `timeDifferenceJet`, :86), after T a compactness argument over histories rescaled at T with
  `eventually_metricComparisonOn_of_local_flow_convergence` (a = −1 < c) against the shrinking cylinder
  (spatial inputs: CapWindowStandardComparison + `exists_far_radial_spatialNeck`,
  StandardFarRegion.lean:400). The equality case (θ₀ = 1/4 has no slack) is removed by taking
  `θ₀ = 1/5` in the predicate, which the S2e computation allows. This is the S2/young-cap-window brick
  (lane SP2), not S1′; S1′ as a standard-solution-only statement is then not needed.
- Strongest fully proved sub-statements delivered for this route: the quarter predicate,
  `TruncatedNeck` with `ofStrongNeck`/`restrictOpen`/`mono`, and the depth-margin jet differentiability.

## Deliverables (round 2)
| File (new) | Lines | Status |
|---|---|---|
| `Surgery/Topology/HistoryStrongNeck.lean` | 169 | quarter predicate + all §1 lemmas + P1; clean |
| `Perelman/CanonicalNeighborhood/TruncatedNeck.lean` | 233 | structure, mono, restrictOpen, jet differentiability, ofStrongNeck; clean |
| `Perelman/CanonicalNeighborhood/StrongNeckRestriction.lean` | 91 | unchanged; clean |
Acceptance order: StrongNeckRestriction → TruncatedNeck → HistoryStrongNeck. Checked via scratch oleans.

## Round 3: θ₀ = 1/5 (lead decision; lane closed)
- Predicate: window conjunct `H.time first ≤ t - 1 / 5 * (G.flow.scalar t y)⁻¹`, neck conjunct
  `Nonempty (TruncatedNeck (…) eps (1 / 5) z t)` (comparison on normalized `Icc (−1/5) 0`).
- S2e inequality restated: `θ₀/R ≤ 2θ₀/λ ≤ 4θ₀r²`, so `t − θ₀/R ≥ T + τ/λ − 4θ₀r² ≥ T − r²` needs
  `θ₀ ≤ 1/4`; `θ₀ = 1/5` is chosen so the window start is STRICTLY after `T − r²`
  (margin `r²/5`), giving the interior slack SP2's compactness route needs.
- Re-verified (one compile per file, scratch oleans): StrongNeckRestriction, TruncatedNeck,
  HistoryStrongNeck all clean; `historyStrongNeck_of_strongNeck` (via `ofStrongNeck` at depth 1/5,
  `d = 1/5 < 1`) and P1 `stronglyCanonicalWhere_of_canonicalBefore` unchanged in statement and
  compile; axioms of all headlines propext, Classical.choice, Quot.sound; `#lint` docBlame only.
- S1′ (standard-solution-only) RETIRED; young cap-window neck goes to SP2 (history level).
- Final files: HistoryStrongNeck.lean 168, TruncatedNeck.lean 232, StrongNeckRestriction.lean 91.
