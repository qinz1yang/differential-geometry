# Lane SL2: T5′ (S leaf from the strong supply), 2026-09-26

Worktree `D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf` @ e68bf6466. No lake build,
nothing staged. Scratch: `scratchpad/sl2` (`cc.sh`: lean.exe directly, `-o` into `sl2/olean`,
LEAN_PATH = sl2 oleans + lake path; nothing under `.lake`).

## Plan
- New `Surgery/Contract/FineCutNeckSupplyStrong.lean`: T4′ def per DESIGN_S_SUPPLY §1(A), predicates
  from SP1's `HistoryStrongNeck.lean` (θ₀ = 1/5 is internal to `HistoryStrongNeck`; the
  `StronglyCanonicalBefore` signature is unchanged).
- New `Surgery/Contract/UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean`: the T5′ theorem, T5
  body with the §4.1 binder chain; private factory helpers via `open private … from`.
- SL1's `StrongNecksOfCutoffClass` is not in the tree yet: elaborated against the §4.1 text in a
  scratch module of the same name (`sl2/src`), to be switched when SL1's file lands.

## Progress
- Scratch oleans for uncommitted SP1 chain: StrongNeckRestriction → TruncatedNeck → HistoryStrongNeck.
- Scratch chain compiled clean (modules renamed `SL2.*` because a same-named `DifferentialGeometry/`
  dir in the first LEAN_PATH entry shadows the build dir).
- `Contract/FineCutNeckSupplyStrong.lean` written (§1(A) verbatim; the predicates' final names in
  `HistoryStrongNeck.lean` match §1(A); θ₀ = 1/5 lives inside `HistoryStrongNeck` so the def text
  is unchanged). Compiled clean, no output. No binder-order fix needed.
- SL1's `Topology/StrongNecksOfCutoffClass.lean` landed during the lane; its def is §4.1 verbatim
  (diffed). My compile uses a scratch copy holding only that def (SL1's module imports its whole
  uncommitted proof chain); the delivered file imports SL1's module.
- `Contract/UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean` written: T5 body with the §4.1
  chain; p₀ bounds abstracted as `∃ x, 0 < x ∧ x ≤ …` packages instead of nested `min` terms.
  First compile: elaboration reached the end, only the olean write failed (path > 260 chars);
  second compile hit a transient missing olean (acceptance build rebuilding
  `CanonicalNeighborhoodsThroughSurgeryStrong`), retrying.
- `CanonicalNeighborhoodsThroughSurgeryStrong.olean` was missing from the shared build 13:48–14:08.
  Work-around (no waiting): its HEAD text and the unmodified committed `UniformDebitSurgeryStepOfFactory`
  compiled as scratch modules `SL2.…` (only those two modules depend on it in the Factory closure);
  `open private … from` rewritten to the scratch module in the scratch copy only.
- Final compile of `UniformDebitSurgeryStepOfFineCutNeckSupplyStrong` (scratch copy, standard linter
  set, 2 threads): no errors, no warnings, no output except the probe. The unused `ρb ≤ 1` package
  entry of T5's ρ-bound was dropped. Probe (scratch copy only, not in the tree):
  `#print axioms uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong` =
  [propext, Classical.choice, Quot.sound]. The three leaves enter as hypotheses, so there is no `sorryAx`.

## Result
| File (new) | Lines | Status |
|---|---|---|
| `Surgery/Contract/FineCutNeckSupplyStrong.lean` | 56 | def T4′, §1(A) verbatim; clean |
| `Surgery/Contract/UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean` | 159 | T5′ proved; clean; axioms std |

Imports of the T5′ module: `Batteries.Tactic.OpenPrivate`, `…Contract.UniformDebitSurgeryStepOfFactory`,
`…Contract.FineCutNeckSupplyStrong`, `…Topology.StrongNecksOfCutoffClass` (SL1).
Acceptance order: StrongNeckRestriction → TruncatedNeck → HistoryStrongNeck (SP1) → FineCutNeckSupplyStrong;
SL1's chain → StrongNecksOfCutoffClass; then UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.
Deferred merge: the four private factory helpers stay private (used via `open private`, as in T5).
No deviation from §4.1's binder chain. Differences from T5: `ε := min εbar (min εF (min εcone εs))`;
`qh` goes into the factory's threshold slot and into T4′ (class clauses lifted by `hqh.trans_lt`);
`p₀` bounds also meet the leaf's `(εh, Dh, mh, δh, ρh)` and the pinching leaf's `(εA, δA, ρA)`, and
`δbound ≤ (2c)⁻¹` gives `InCutoffClass` through `CutoffParameters.recenterConstant_mul_le_half`.
T4′ has no p₀ constraint, so T5's `Rrad ζ₀ δ₀ ρ₀ m₀` slots are replaced by the leaf's.

## Skeleton edit for the acceptance lane (`Surgery/Skeleton/PoincareEndgame.lean`)
Add `import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.UniformDebitSurgeryStepOfFineCutNeckSupplyStrong`
and replace the S leaf (`theorem uniformDebitSurgeryStepStrong … := by sorry`) by:
```lean
theorem fineCutNeckSupplyStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    FineCutNeckSupplyStrong P₀ g₀ := by
  sorry

theorem strongNecksOfCutoffClass (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    StrongNecksOfCutoffClass P₀ g₀ := by
  sorry

theorem uniformDebitSurgeryStepStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    UniformDebitSurgeryStepStrong P₀ g₀ :=
  uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (strongNecksOfCutoffClass P₀ g₀) (fineCutNeckSupplyStrong P₀ g₀)
```
`pinchingThroughSurgery` is the proved theorem of the imported `Topology/PinchingThroughSurgery.lean:12`,
so no reordering is needed. The binders force nothing else: `hext_of_…Strong` takes `hstep : ∀ P₀ g₀`
with no `SimplyConnectedSpace` instance, and none of the three inputs needs one. If SL1's
`strongNecksOfCutoffClass_of_strongSpatialCrossing` is wired instead, the second leaf becomes
`strongSpatialCrossingContinuation … := by sorry` and `strongNecksOfCutoffClass P₀ g₀ :=
strongNecksOfCutoffClass_of_strongSpatialCrossing P₀ g₀ (strongSpatialCrossingContinuation P₀ g₀)`.
