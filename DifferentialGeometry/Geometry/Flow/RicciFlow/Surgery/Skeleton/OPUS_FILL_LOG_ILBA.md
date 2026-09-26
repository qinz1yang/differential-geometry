# Lane ILBA: brick 24a (quantitative cap-point action barrier), `ANALYSIS_ILB.md` §"24a"

Paths relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/`. Worktree pc3 at e68bf6466.
Scratch: session scratchpad `ilba/` (`gen.sh` remaps imports of the CP2-relocated modules to CP2's scratch
oleans `CP2S.*` / `CP2C.*` under `cp2/out`, read-only; `cc.sh` = lean.exe direct, 2 threads, lakefile options).
Scratch module names: `ILBA.G1`, `ILBA.A24`.

## Result (2026-09-26)

| File (new, untracked) | Lines | Compile |
|---|---|---|
| `CapWindowActionRegularCrossingBefore.lean` | 491 | clean, 0 messages (71 s) |
| `RegularMinimizerEndpointBarrier.lean` | 61 | clean, 0 messages (48 s) |

Axioms (`#print axioms`, scratch probe, removed): `exists_uniform_regularMinimizerEndpoint_of_regularizedCost_lt`,
`ObservedHistory.exists_uniform_regularCrossing_minimizer_of_regularizedCost_lt_of_derivative_before`,
`ObservedHistory.abs_derivWithin_stageScalar_le_of_le_of_forall_lt`: `[propext, Classical.choice, Quot.sound]`.
No sorry/axiom/nolint/heartbeats/comments/docstrings. Name clashes: none (grep of every new name, whole tree).

## G1 (strict cutoff): how it was closed

- Every use of the derivative hypothesis inside the relocated chain (`WindowEvolution`, `PreparedCapCommonFlow`,
  `FirstCapDiscarding` via `hevents`/`hfinal`) is at times `v < t`, but the chain's statements (`:29`, `:173`,
  `:383`) ask for `v ≤ t` and the `:530 … :1079` wrappers ask for ALL times. Re-threading below `:383` would
  copy ~800 lines; instead the non-strict form is DERIVED from the strict one at the one point `s = t`
  (interior of the stage) by continuity of `R` and of `derivWithin (·) (Iic s) s` in time:
  - `OrientedThreeStage.ClosedSlab.abs_derivWithin_scalar_le_of_forall_Ioo` (new; ClosedSlab twin of the
    committed `IncomingSlab.abs_derivWithin_scalar_le_of_forall_Ioo`, `SliverForwardComparison.lean:143`),
  - `ObservedHistory.abs_derivWithin_stageScalar_le_of_forall_Ioo` (stage dispatch: event slab / final slab),
  - `ObservedHistory.abs_derivWithin_stageScalar_le_of_le_of_forall_lt` (strict ⇒ `s ≤ t`).
- Re-threaded copies (statement change only: the derivative hypothesis moved after `t` and gets `s < t.val`;
  proofs verbatim except the `:383` call site, which now receives the derived `s ≤ t` form):
  `…_gt_of_inserted_cap_birth_of_derivative_before` (`:530`), `…_gt_of_nonregular_node_of_derivative_before`
  (`:614`), `exists_uniform_regularCrossing_of_sum_stageRegularizedAction_lt_of_derivative_before` (`:861`,
  uses the private `exists_contMDiff_family_action_lt` through `open private … from`),
  `exists_uniform_regularCrossing_minimizer_of_regularizedCost_lt_of_derivative_before` (`:1079`; also drops the
  unused `B` from its argument list, `hB` is built internally as in the original).
- Deferred merge: once CapWindowActionRegularCrossing is committed, the four originals are corollaries of the
  `_of_derivative_before` versions (all-times hypothesis ⇒ strict one); or the originals can be restated. Not
  done here (no edits to relocated/committed files).

## G2 / G3

- `a₀`: `exists_pos_fixedHamiltonIveyRegion_for_identified_histories` (`HamiltonIveyPinching.lean:666`) gives both
  `InFixedHamiltonIveyRegion (initialMetric 0) a₀` and `-3/a₀ ≤ R(initialMetric 0)`; depends on `(P₀, g₀)` only.
- Records: `hasCanonicalCutoffRecords` unpacks to the raw `parameters`, `records`, canonical windows, `delta`/`neckRadius`
  bounds; model parameters transported by the record equalities.
- `mono_radius`, `stageMetric = incoming.flow.scalar` and the stage floor G3 are NOT needed: the ball radius is the
  given `r₀`, the stage identification is internal to G1's dispatch lemma, and the `3/a₀` floor is produced inside
  the `:1079` proof (`fixedHamiltonIveyRegion_and_scalar_lower`).

## Statement deltas vs `ANALYSIS_ILB.md` (reasons)

1. `B`, `0 < B`, `H.horizon < B`, `v ≤ √B` replaced by a free bound `E` with `v ≤ E` (no sign condition):
   the horizon bound was unused and `B` only entered through `v ≤ √B`; the proof passes `max E 0`. The leaf takes
   `E := √B`.
2. `InitialIdentification P₀ g₀ H.toHistory →` weakened to `Nonempty (InitialIdentification …) →` (the leaf has
   exactly `hH.1` of `InCutoffClass`).
3. `HistoryScalarDerivativeBoundBefore` defined exactly as in the analysis (top level of `…Surgery.Topology`).
Everything else (quantifier order, `(δ₀ ε₀ R₀ m₀)`, `Λ`, `ρ`, the `3 / a₀` floor, conclusion) is as specified.

## What 24b / the leaf still need from 24a

- Nothing more from the barrier: `cost < A ⇒ q ∈ regularMinimizerEndpoints` for all `first ≤ activeStage t`, `v ≤ E`.
- Leaf glue (not done here): produce `HistoryScalarDerivativeBoundBefore H Ctime qcan t` from `EventSlabsDerivative`
  + `DerivativeBoundBefore t₀` (`t ≤ t₀`; later stages are vacuous since `s < t ≤ time`), and on
  `extendHorizon T` for the terminal clause; the `Λ` bound on `p₀.recenterConstant` (interface finding 1) is still
  missing from `HistoryReducedVolumeInitialLowerBound`.
- Acceptance: both files import the relocated `CapWindowActionRegularCrossing` (CP2); register both in the root
  aggregate after CP2's files.
