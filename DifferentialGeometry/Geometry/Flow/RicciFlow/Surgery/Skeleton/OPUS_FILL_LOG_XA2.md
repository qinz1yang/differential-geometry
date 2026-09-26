# OPUS fill log XA2 — bricks X1 (+X1e, X1k) and X6b of DESIGN_CROSSING_ASSEMBLY.md

Worker: Opus 5.5, worktree D:\differential-geometry-pc3 (codex/pc-target-c-psf), started 2026-09-26.
Scratch: C:\Users\liao9\AppData\Local\Temp\claude\D--differential-geometry-moise-int\08693914-694c-4a5b-8767-edd7f4799e4d\scratchpad\xa2

## Status
- X1k: compiled clean (RetainedCoreHistoryExtendAt.lean)
- X6b: compiled clean (CrossingClauseTransport.lean + CanonicalWitnessTimeRestrict.lean)
- X1e: compiled clean (RetainedCoreHistoryPrefixInvariants.lean)
- X1: compiled clean (CrossingBadPoint.lean)
- ALL DONE 2026-09-26; final re-compile of all five modules (scratch, standard linter set): zero output.

## Method
- Compile: committed-import files directly with `lake env lean` (quoted -D flags; PowerShell splits
  unquoted `-Dweak.linter...`). Files importing my uncommitted modules: scratch copies
  `XA2Scratch.<Name>` under scratch/src with rewritten imports, `lean -R scratch/src -o scratch/olean/...`,
  LEAN_PATH = scratch/olean + lake's LEAN_PATH (scripts sync.sh / s.ps1 in scratch). Nothing under .lake.

## X1k (2026-09-26)
- File `Surgery/Topology/RetainedCoreHistoryExtendAt.lean`: `RetainedCoreHistory.extendAt`, `extendAtTime`
  (defs verbatim from §2.2), `capWindowPoint_extendHorizon_iff` (verbatim). records' is the existing
  `GeometricCutoffRecord.extendHorizon` (CutoffRecordHorizonExtension:24); the iff re-packs traces
  as in BoundedCurvatureAtDistanceSlice:200.

## X6b (2026-09-26)
- New reusable file `Perelman/CanonicalNeighborhood/CanonicalWitnessTimeRestrict.lean`:
  `StrongNeck/LocalNeck/OrderedNeckChain/LocalCap/RoundComponent/CanonicalAlternative/CanonicalWitness.timeRestrict`
  (a witness of `S` is one of `S.timeRestrict D'` whenever `D.carrier ⊆ D'.carrier`) and
  `CanonicalWitness.capTubeHasNeckChart.timeRestrict`. Modelled on CanonicalToleranceMonotone.
- File `Surgery/Topology/CrossingClauseTransport.lean`: `RetainedCoreHistory.canonical_clauses_of_extendAt`,
  the §2.9 statement with `S` and `a` spelled out (S := closedPrefixAt flow of the extended history at
  extendAtTime, a := its active-stage time). Route: constant upgrade on S (own private copy of
  `canonical_bounds_of_canonicalWitness_of_scalar_derivative_bounds` WITHOUT its `hR : 0 ≤ R`
  hypothesis, which the §2.9 statement does not carry: `R·√R ≥ 0` holds for every real R), then
  generalize the active stage (`subst` on `activeStage τ = k`), base equality from
  `closedPrefixAt_metric` + `stageMetric_extendHorizon_last`, witness via `timeRestrict`
  (`Icc a t ⊆ Ico a s`).

## X1e (2026-09-26)
- File `Surgery/Topology/RetainedCoreHistoryPrefixInvariants.lean` (156 lines). Statements (the design
  lists them by name only; these are the natural forms, conclusions at `H.prefixAt k` / `Fin.last _`):
  - `inCutoffClass_prefixAt (hH : H.InCutoffClass g₀ B p₀ δ ρ) (k) : (H.prefixAt k).InCutoffClass g₀ B p₀ δ ρ`
    (identification via `InitialIdentification.of_stageZero`, records via `prefixRecords` +
    `isCanonicalCutoffRecordFamily_prefixAt`);
  - `eventSlabsCanonical_prefixAt`, `eventSlabsGradient_prefixAt`, `eventSlabsSpatiallyCanonical_prefixAt`
    `(k) (h : … k) : (H.prefixAt k).… (Fin.last _)`;
  - `noncollapsedBefore_prefixAt (k) (h : H.NoncollapsedBefore κ ρ t) (ht : H.time k ≤ t) :
    (H.prefixAt k).NoncollapsedBefore κ ρ (H.time k)` — proof as `noncollapsedBefore_eventPrefix`, with
    two new helper theorems `prefixAt_activeStage_val` and `prefixAt_stageMetric_activeStage` (at the
    active stage the prefix metric equals H's; the last-stage case uses τ = time k and
    `stageMetric_initial`).
- The two private helpers of RetainedCoreHistoryPrefixTransport (`rm_bound_of_stage_eq`,
  `volume_lower_bound_of_stage_index`) are used via `open private … from`, not copied (no deferred merge).

## X1 (2026-09-26)
- File `Surgery/Topology/CrossingBadPoint.lean` (88 lines): `RetainedCoreHistory.exists_crossing_bad_point_terminal`,
  statement verbatim from §2.2. η := min(min η₀ η₁)(min δ (ς/S)) with η₀ from `hext`, η₁ from
  `exists_sliver_forward_comparison` (K := max(sup riemannNorm at t₀, 1) via
  `exists_forall_Icc_riemannNorm_le`), δ from BS1 at ζ', S from BS4; `R·η ≤ ζ` by sign split
  (R < 0 trivially). Bad point from `¬ CanonicalBoundsOn` at this η.

## Axioms (all `propext, Classical.choice, Quot.sound`; no sorryAx; probe deleted)
extendAt, extendAtTime, capWindowPoint_extendHorizon_iff, canonical_clauses_of_extendAt,
CanonicalWitness.timeRestrict, CanonicalWitness.capTubeHasNeckChart.timeRestrict,
exists_crossing_bad_point_terminal, inCutoffClass_prefixAt, eventSlabsCanonical/Gradient/SpatiallyCanonical_prefixAt,
noncollapsedBefore_prefixAt, prefixAt_activeStage_val, prefixAt_stageMetric_activeStage.
New public names grep-unique library-wide. Not registered in DifferentialGeometry.lean (lead's job).

## Deviations
- None in statements. X6b's §2.9 abbreviations `S`, `a`, `√`, `g_t` are spelled out in full.
- X6b does not use `canonical_bounds_of_canonicalWitness_of_scalar_derivative_bounds` (AncientLimitCanonicalWitness:29)
  because that lemma needs `hR : 0 ≤ R`, absent from the §2.9 statement; a private copy without `hR`
  is used instead (the hypothesis is unnecessary there too — candidate cleanup when that file is next touched).
- X6b needed a reusable witness transfer to a larger time domain: new file
  `Perelman/CanonicalNeighborhood/CanonicalWitnessTimeRestrict.lean` (162 lines).
- Root-aggregate registration of the five new modules: pending (lead).
