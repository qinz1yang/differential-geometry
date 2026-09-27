# SB4 — brick B4: discarded classification (A2) on spatial witnesses (2026-09-26)

Worktree `D:\differential-geometry-pc3`. Paths relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/`.
No git writes, no `lake build`.

## Progress
- Start. Read AGENTS.md (pc3: no headers/docstrings), NAMING §2–6, Skeleton/README, DESIGN_S_FACTORY
  (§1 S4, B4), OPUS_FILL_LOG_SB3, OPUS_FILL_LOG_SFM, current working-tree A2 files
  (DiscardedCanonicalCoverage, TerminalComponentClassification, DiscardedComponentClassification,
  StoppedCapCuttingSide), SpatialCanonicalWitness, SpatialCanonicalWitnessTransport,
  CompactCanonicalCover, CanonicalNeighborhoodInduction (SpatiallyCanonicalBefore, DerivativeBoundBefore).
- Site audit of S4 (witness reads): (a) coverage `exists_late_canonical_on_discarded_core…` re-exports
  witnesses, reads nothing but the derivative clause (already separate); (b) cutting side
  (StoppedCapCuttingSide:385/531) reads `one_le_comparison_constant`, `Q_pos`, `scalar_bounds`, `domain`,
  and the `alternative` (neck → contradiction with stopped; positive/round → `whole`, excluded;
  cap → truncated cap core + ball in interior via `depth`) — all slice data; (c) component classification
  (CompactCanonicalCover:345 via TerminalComponentClassification:72) reads the full alternative
  restricted to the component (neck restriction, positive, round, cap core on the component).
  No backward-window (`StrongNeck`) field is read anywhere in S4: the only `StrongNeck` use is
  `data.strong.toSpatialNeck` (slice). Nothing to isolate.
- Compile method attempt 1: scratch olean mirror (E:\sb4-mirror, junctions + hard links) to get an
  olean for the uncommitted `TerminalSpatialCanonicalAlternatives`; abandoned because the lead's
  `lake build` (started 04:30) was rebuilding this build dir and it produced exactly the oleans needed
  (TerminalSpatialCanonicalAlternatives 04:35, SFM-edited DiscardedCanonicalCoverage 04:33,
  DiscardedComponentClassification 04:34). Mirror removed (junctions unlinked first, then its own hard
  links; real build tree untouched). From then on: plain `LEAN_NUM_THREADS=2 lake env lean <file>`.
- File 1 `Surgery/Topology/CompactComponentSpatialClassification.lean` compiles with no output
  (one fix: selective `open DifferentialGeometry.CheegerGromovCompactness (metricScalarAt_restrictOpen)`).
- File 2 `Surgery/Topology/DiscardedSpatialClassification.lean` written; it imports file 1 (no olean,
  no lake build), so checked by concatenating both files into a scratch file outside the repo.

## Outcome: B4 PROVED, sorry-free (2 new files, 323 + 410 lines; nothing else edited)

### Headline (A2), original vs new
Original `GeometricCutoffRecord.exists_poincareStandardDiscarded_tolerance_of_canonical_neighborhoods`
(DiscardedComponentClassification, working tree after SFM), hypotheses after `hscale`:
```
(∀ x : (H.stage i.castSucc).Carrier, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
   q < (H.event i).incoming.flow.scalar t x →
     ∃ W : CanonicalWitness (H.event i).incoming.flow eps C1 C2 x t, W.capTubeHasNeckChart eps) →
∀ Ctime : ℝ≥0, (∀ x, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), q < … →
   |derivWithin (fun v => (H.event i).incoming.flow.scalar v x) (Iic t) t| ≤ Ctime * … ^ 2) →
SmoothCutCapCompletion (H.event i).transition → (H.event i).poincareStandardDiscarded
```
New `GeometricCutoffRecord.exists_poincareStandardDiscarded_tolerance_of_spatiallyCanonical`:
```
∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
  ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (parameters : CutoffParameters)
    (G : GeometricCutoffRecord H i parameters), (∀ j, G.delta j ≤ eps) →
    ∀ C1 C2 q : ℝ, 1 ≤ C2 → 0 < q → q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
      (∀ j, C2 ^ 2 * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ < (G.neck j).scale) →
      (H.event i).incoming.SpatiallyCanonicalBefore eps C1 C2 q (H.time i.succ) →
      ∀ Ctime : ℝ≥0, (H.event i).incoming.DerivativeBoundBefore Ctime q (H.time i.succ) →
      SmoothCutCapCompletion (H.event i).transition → (H.event i).poincareStandardDiscarded
```
Conclusion and all other binders verbatim. `DerivativeBoundBefore Ctime q s` unfolds to exactly SFM's
clause (`∀ y t, t ∈ Ioo a s → q < R → |∂ₜR| ≤ Ctime R²`), so the factory can pass its clause unchanged.

### Siblings (file 2, ns `…Surgery.Topology.GeometricCutoffRecord`)
- `exists_late_spatiallyCanonical_on_discarded_core` ← DiscardedCanonicalCoverage
  `exists_late_canonical_on_discarded_core_with_cap_neck_charts_of_canonical_neighborhoods`:
  hypotheses `SpatiallyCanonicalBefore eps C1 C2 Q (H.time i.succ)` + `DerivativeBoundBefore Ctime Q …`;
  conclusion re-exports `∃ W : SpatialCanonicalWitness ((H.event i).incoming.flow.base.metric t) eps C1 C2 z.val,
  W.capTubeHasNeckChart eps` (instead of `CanonicalWitness … z.val t`).
- `exists_late_not_closedBand_subset_spatialWitness_domain_of_cutting_scale` ← StoppedCapCuttingSide:385
  (quantifies over spatial witnesses; reads `one_le_comparison_constant`, `Q_pos`, `scalar_bounds`).
- `exists_late_capCore_cutting_side_of_stopped_cylinder_of_spatialWitness` ← StoppedCapCuttingSide:531
  (same statement with `W : SpatialCanonicalWitness (g t) eps C1 C2 (nk.map (nk.center, a))`).
- private `exists_isPoincareStandard_discarded_boundary_tolerance_of_spatiallyCanonical` ← private
  DiscardedComponentClassification:22.

### Siblings (file 1)
- ns `…FiniteHorn`: `SpatialCanonicalWitness.exists_capCore_with_neck_frontier` (spatial copy of the private
  CompactCanonicalCover:29, plus the ball-in-interior conclusion every consumer recomputed; uses SB3's
  `SpatialLocalCap.exists_truncated_compactDomain`/`nonempty_capCore_truncated_core`);
  `SpatialCanonicalWitness.exists_capCore_on_connectedComponent` (← private CompactCanonicalCover:275);
  `def SpatialRoundComponent.restrictOpen` (← private `roundComponentRestrictOpen`, :193);
  `SpatialCanonicalWitness.spatial_cap_or_whole_on_connectedComponent_of_not_spatial_neck` (← :345).
- ns `…Surgery.Topology`: `isPositiveSpaceFormModel_of_spatialRoundComponent` (← PoincareStandardGeometricFrontier:111);
  `exists_compact_component_spatial_poincareStandard_tolerance` (← CompactCanonicalClassification:32, witnesses
  `∀ x : (M.component c).Carrier, SpatialCanonicalWitness g eps C1 C2 x.val` on a bare metric `g`).
- ns `…IncomingSlab`: `exists_component_poincareStandard_tolerance_of_spatiallyCanonical`
  (← TerminalComponentClassification:72; witness clause → `G.SpatiallyCanonicalBefore eps C1 C2 q s`,
  derivative clause → `G.DerivativeBoundBefore Ctime q s`; conclusion verbatim).

### Site notes
- Backward window: never read. The only `StrongNeck` use in the originals was `data.strong.toSpatialNeck`;
  the spatial `neck` alternative carries a `SpatialNeck` directly. Nothing isolated.
- Young round `S³` (review 3 F5): handled by the spatial `round` alternative. In the component
  classification it is restricted to the component (`SpatialRoundComponent.restrictOpen`, whole = component)
  and turned into `IsPositiveSpaceFormModel`; `positive` is restricted via the existing private
  `positive_component_restrictOpen` (`open private`). In the cutting-side step both whole-component
  alternatives are excluded exactly as before (`W.domain = connectedComponent` contradicts the band exclusion).
- Chart accuracy: all spatial leaves take `W.capTubeHasNeckChart eps` at the witness accuracy, as in the
  factory (`epsTop` for both).
- Not restated: `exists_poincareStandardDiscarded_cutting_scale(_of_incoming)` — they take no canonical
  hypothesis (they build intrinsic witnesses from the slab), so they have no `epsTop` input to swap.
- For the factory swap (B8): the private `exists_poincareStandardDiscarded_of_retainedEvent_heq_tolerance`
  (PoincareHornCutoffRecord:447) needs an HEq transport of `SpatiallyCanonicalBefore` (analogue of
  `canonical_neighborhoods_of_incoming_heq`); not done here (Contract file edits out of scope).

## Verification
- File 1: `LEAN_NUM_THREADS=2 lake env lean -Dweak.linter.mathlibStandardSet=true <file1>`: no output.
  Imports resolved against oleans produced by the lead's concurrent `lake build` (04:30–, incl. SB3 file 1 and
  the SFM-edited A2 modules).
- File 2 (imports file 1, no olean): both files concatenated into one scratch file outside the repo;
  `lake env lean -Dweak.linter.mathlibStandardSet=true`: no diagnostics from the real content; `#lint`:
  12 declarations, 14 linters, only `docBlame` on the `def` (inapplicable per AGENTS.md).
  One `unusedArguments` finding (`[SigmaCompactSpace U]` on `restrictOpen`) fixed by removing the binder.
- Axioms (scratch): headline, component sibling, cutting-side sibling, coverage sibling, compact component
  classification, round → space-form, cap-or-whole: `[propext, Classical.choice, Quot.sound]`.
- Lines ≤ 100 chars (imports excepted); only option `set_option autoImplicit false`; no sorry/nolint/
  heartbeat overrides; no comments/docstrings/headers. New public names grepped unique. Not registered in
  the root aggregate. Scratch removed. No git writes, no lake build.
