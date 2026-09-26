# OPUS fill log SL1: StrongNecksOfCutoffClass leaf assembly (2026-09-26)

Worker lane SL1. Scope: (1) named brick `StrongSpatialCrossingContinuation` (SX with the strong
conclusion) + `→ SpatialCrossingContinuation`; (2) the A-lite leaf `StrongNecksOfCutoffClass`
(DESIGN_STRONG_INTERFACE §4.1 verbatim) and `strongNecksOfCutoffClass_of_strongSpatialCrossing`.
New files only; read-only compiles via scratch chain `scratchpad/sl1` (modules renamed `SL1S.*`,
`lean -o`, LEAN_PATH = scratch out + `lake env`); no git writes, no lake build, no root aggregate.

## Progress

- 00:00 read pc3 AGENTS.md (imports first, no header/module docstring, zero comments), §4 of
  DESIGN_STRONG_INTERFACE, SX (`SpatialCrossingContinuation.lean`), SP1/SP2 logs and files, the class
  predicates (`CanonicalNeighborhoodInduction.lean`, `…ContinuationLeaves.lean`).
- Scratch chain: StrongNeckRestriction → TruncatedNeck → HistoryStrongNeck; SpatialCanonicalWitnessFrontier
  → StandardCapSpatialCanonical → StandardWindowCapWitness → CapWindowCapWitness; SpatialCrossingContinuation.
- Plan (η-window): the leaf has the WHOLE-slab class as hypothesis, so no event induction is needed for
  case (iii): at a point `(y, t)` apply the brick with `t₀ := t`, `η₃ := (slab end) − t`; the brick's
  `…On t₀ η₃` inputs are restrictions of the whole-slab `…Before` clauses; its output window
  `[t₀, t₀ + η)` contains `t`.
- Scratch chain compiled (host olean-read failures on the first attempt, retried): all clean.
- DONE (1): `Surgery/Topology/StrongSpatialCrossingContinuation.lean` (116 lines): def
  `StrongSpatialCrossingContinuation` = SX verbatim with (a) prefix `∀ ε₁ : ℝ, 0 < ε₁ → ε₁ < 1 / 11 →`,
  (b) `εbar ≤ ε₁` added after `εbar ≤ coneAccuracy`, (c) both conclusions
  `∃ W : SpatialCanonicalWitness (…metric t) ε Cx Cx y, W.capTubeHasNeckChart ε ∧
  ((∃ n, W.alternative = .neck n) → H.toHistory.HistoryStrongNeck <slab> <G> ε₁ y t)`
  (event: `j.castSucc`, `(H.toHistory.event j).incoming`; terminal: `Fin.last _`, `G`) — i.e.
  definitionally `H.StronglyCanonicalAt … ε ε₁ Cx Cx y t`. Everything else (binder order, `0 < ε`,
  `ε < 1/11`, `∃ Cx` before `∀ B`, `θ` input, `∃ Dcap θcap q₀ mcap`, `∀ qcan ≥ q₀ ∃ δmax ρmax εcap`,
  `qs ∈ [qcan, Cs·qcan]`, C3 output as `∀ η₃ > 0, …On t₀ η₃ →` input) is SX's text unchanged.
  `spatialCrossingContinuation_of_strongSpatialCrossingContinuation` proved (instantiate `ε₁ := 1/12`,
  drop the implication). Compile clean, 0 warnings (linter set on).
- DONE (2): `Surgery/Topology/StrongNecksOfCutoffClass.lean` (155 lines): def `StrongNecksOfCutoffClass`
  byte-identical to DESIGN_STRONG_INTERFACE §4.1 (diffed), and
  `strongNecksOfCutoffClass_of_strongSpatialCrossing (hcross : StrongSpatialCrossingContinuation P₀ g₀) :
  StrongNecksOfCutoffClass P₀ g₀` PROVED. Compile clean, 0 warnings.

## Proof of the leaf (constant wiring)
- `εbar := ` brick's `εbar(ε₁)` (so `ε ≤ ε₁`, `ε < 1/11`); `Cx` from the brick at `ε`.
- Brick instantiated with `Cs := 1`, `θ := τmin`; gives `Dcap θcap q₀ mcap`. SP2
  (`exists_capWindow_stronglyCanonicalWhere`) with `Dw := Dcap`, the brick's `θcap`: gives `Cs Rcap mw`.
- `qh := max qcan q₀`; brick at `qcan := qh`, `qs := qh`; SP2 at `qh`.
- Output: `C1h := max C1 (max Cs Cx)`, `C2h := max C2 (max (max Cs Cgrad) Cx)`, `δmax/ρmax/εcap := min`
  of brick's and SP2's, `Dcap_leaf := Rcap` (> brick `Dcap + 1`), `mcap := max mcap mw`.
- Records: `hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily` on `hH.2.2.2.1`; the SAME
  `records` feed SP2 and the brick, so the cap-window predicate splits consistently.
- Class clauses lifted from `qcan` to `qh` pointwise (threshold monotonicity), restricted from
  `Fin.last` to `j.castSucc` by `Fin.castSucc_lt_last`.
- Per slab (generic `key`): cover `τmin ≤ R(t−a)` (SP1 P1 + `mono_constants`) / `CapWindowPoint Dcap θcap`
  (SP2 + `mono_constants`) / `R(t−a) < τmin ∧ ¬CapWindowPoint` (brick) via `le_or_gt` + `by_cases` and
  `stronglyCanonicalBefore_of_where_cover`.
- Young non-cap-window point `(y,t)`: brick with `t₀ := t`, `η₃ := (slab end) − t`; its `…Before t₀`
  inputs are `*_mono` of the whole-slab clauses, `NoncollapsedBefore κ ε t` by `noncollapsedBefore_mono`
  (event) / the leaf's `∀ t₀ ∈ Ioo, TerminalNoncollapsedBefore` (terminal), its `…On t η₃` inputs are
  restrictions of the whole-slab `…Before`; the output window `[t, t+η)` contains `t`.
  DEVIATION from the task text: no event induction is needed — the leaf's hypotheses are the whole-slab
  class on every slab, so the brick is fed at `t₀ := t` directly (no previous-window induction).
- Axioms (probe removed): both theorems `propext, Classical.choice, Quot.sound`; no `sorryAx`.
  `#lint`: only docBlame (excluded). Names unique library-wide; the existing uncommitted consumer
  `Contract/UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean` already imports this module name.

## Result
| File (new) | Lines | Status |
|---|---|---|
| `Surgery/Topology/StrongSpatialCrossingContinuation.lean` | 116 | clean (scratch oleans) |
| `Surgery/Topology/StrongNecksOfCutoffClass.lean` | 155 | clean (scratch oleans) |
Acceptance order: SP1 chain (StrongNeckRestriction → TruncatedNeck → HistoryStrongNeck), SX
(SpatialCrossingContinuation), SP2 chain (SpatialCanonicalWitnessFrontier → StandardCapSpatialCanonical
→ StandardWindowCapWitness → CapWindowCapWitness), then StrongSpatialCrossingContinuation →
StrongNecksOfCutoffClass. Not registered in the root aggregate.
