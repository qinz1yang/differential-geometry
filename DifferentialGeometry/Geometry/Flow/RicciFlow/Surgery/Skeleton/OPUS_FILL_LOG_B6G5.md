# B6g5 — DESIGN_B6D_GLUE brick B13 (composed headline), 2026-09-26

- Start. Read AGENTS.md (pc3), DESIGN_B6D_GLUE.md §0–§2, H7 digest, OPUS_FILL_LOG_B6G3/B6G4,
  suppliers: TimeControl variant (`…_of_noncollapsed_before`), B11 (ShiftedTransfer), B6
  (`TracedRegionAncientLimitNeckAlternatives`), B12 (`TracedRegionAncientLimitDerivativeCutoff`,
  `abs_derivWithin_scalar_le_of_survivor_maps_of_lt` — exactly B11's `hderiv` shape, so B12 not BS2).
- Scratch chain (own dir `scratchpad\b6g5\`, renamed modules `B6G5.*`, 2 threads, live shared oleans
  for committed prereqs; C: scratchpad cannot hard-link E: oleans): ManifoldUniformComparison,
  EarlierTimeVolume, ShiftedTransfer, UniformMetricTimeLipschitz, TerminalNoncollapsing,
  LocalMetricTimeLipschitz, TimeControl.
- New file: `Surgery/Topology/TracedRegionAncientLimitScalarBound.lean`.

## DONE (2026-09-26) — B13 proved, unconditional

File: `Surgery/Topology/TracedRegionAncientLimitScalarBound.lean` (326 lines), ns
`Surgery.Topology.ObservedHistory`, imports TimeControl, ShiftedTransfer, B6 (`…NeckAlternatives`),
B12 (`…DerivativeCutoff`). Nothing committed/staged; root aggregate untouched; no committed file edited.

`exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before`:
`∃ epsW > 0, ∀ H t y R hR, hRlim → htraced → ∀ {κ ρ}, 0<κ → 0<ρ → ∀ {t₀}, hsliver → hnc(v < t₀ n) →
∀ {Phi}, hPhi → hpinch(v ≤ t n) → ∀ {eps C1 C2 Cs Cq} {Ctime : ℝ≥0} {qs qcan}, 0<eps → eps ≤ epsW →
(qs n ≤ Cs·R n) → (qcan n ≤ Cq·R n) → hwit(v < t₀ n) → hderiv(v < t₀ n) →` the conclusion of
`exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_noncollapsed_before`
VERBATIM, with the κ clause parenthesised and `∧ ∃ C, ∀ s ≤ 0, ∀ x : P.M, metricScalarAt (G s) x ≤ C`
appended.

Deltas vs DESIGN_B6D_GLUE §2 B13 (recorded):
1. Conclusion = the κ-before variant's conclusion (per-k κ clause gated by `t n + σ/R n < t₀ n`;
   extra limit clause `∀ ρ' > 0, ParabolicallyKappaNoncollapsedBelowScale … (κ/250) ρ'`), not B6b′'s.
2. `hnc` restricted to `(v : ℝ) < t₀ n` (H7 decision 2).
3. `ht₀ : ∀ n, t₀ n ≤ t n` DROPPED: unused. If `t₀ n > t n` the set `{s ≤ 0 | t₀ ≤ t + s/R}` is empty,
   so `E n \ Icc (-ζ n) 0 ⊆ {R(time i − t)}` holds regardless. The Crossing leaf may still pass it
   (it is simply not a hypothesis).
4. Hypotheses are otherwise the design's, as named binders inside the ∀ chain. No Prop packaging;
   only `v < t₀ n` witnesses/derivative bounds/κ, `hsliver`, `qs ≤ Cs·R`, `qcan ≤ Cq·R`, `eps ≤ epsW`.

Proof: variant → W,h,…; `C := max 1 (max (2|C1|) C2)` (H7 clamp, `1 ≤ C` for B11);
`qW := max Cs (e·(C + (D + 2ε⁻¹)√C))²` with B6's `D`; `qD := Cq`; `L := e` (`e² = exp 2` = B7 lower
bound); `E n := Iic 0 ∩ ({s | t₀ n ≤ t n + s/R n} ∪ {s | ∃ i, t n + s/R n = time i})`,
`ζ n := R n (t n − t₀ n)` (hζ = hsliver; finiteness via range of `i ↦ R(time i − t)` over
`Fin (eventCount+1)`); `s ∉ E n` gives `t + s/R < t₀` and `time(activeStage v) < v`
(`activeStage_time_le` + `≠`). hW: B6 at level `θ = 2(k+2)` with the per-k survivor maps, then
weakened from `max (2|C1|) C2` to `C` (strict threshold margin `e·(C0+…) ≤ e·(C+…) < √scalar` via
`Real.lt_sqrt`); unit `h 0`-ball compact via `isCompact_riemannianClosedBallOf_restrictOpen` (ball
`k+1` + 1 < `k+3`). hderiv: B12 `abs_derivWithin_scalar_le_of_survivor_maps_of_lt`. Pinching on `h`:
copy of TimeControl's `hpinchW` (`curvatureOperatorLowerBoundAt_localPullMetric_iff`,
`_scaleMetric_iff`), Q := R. Then B11.
- `open private` from TracedRegionAncientLimit: `scaleMetric_restrictOpen`, `mem_Icc_of_mem_window`,
  `isCompact_riemannianClosedBallOf_restrictOpen` (lead: these three want to be public).
- Verification: scratch module `B6G5.ScalarBound` against the scratch chain (2 threads): no output.
  `#print axioms`: `[propext, Classical.choice, Quot.sound]`. `#lint in B6G5` (14 linters): 0 errors in
  38 declarations. Lines ≤ 100, no comments/docstrings, name unique library-wide. Not compiled in-repo
  (its uncommitted imports TimeControl/ShiftedTransfer have no shared olean yet). Scratch dir removed.
- Acceptance: register `…Surgery.Topology.TracedRegionAncientLimitScalarBound` (after TimeControl,
  ShiftedTransfer and their uncommitted prereqs) in the root aggregate.
