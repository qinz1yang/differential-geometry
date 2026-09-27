# OPUS_FILL_LOG_C4A (DESIGN_C4_ASSEMBLY §2 first row: I29 prep, P0 + (A), SX def, leaf assembly L)

## 2026-09-26 entry 1 (start)

Read: pc3 AGENTS.md (new files begin with imports, no module docstring, no comments),
DESIGN_C4_ASSEMBLY.md §0–§3, H16 digest, M5 (`CapWindowSpatialCanonicalWitness.lean`, uncommitted),
`SpatialCanonicalContinuation.lean`, `CanonicalNeighborhoodsThroughSurgeryStrong.lean` (working copy
carries someone else's uncommitted `[SimplyConnectedSpace P₀.Carrier]` diff in two `hcn` binders; not
touched).

Compile method: own scratch `scratchpad/c4a` (`lc.sh`, copy of C4B3's with prefix `C4A`). M5's five
C4B2 prerequisites are now committed (e3d854792) with shared oleans, so only M5 is a scratch module
(`C4A.CapWindowSpatialCanonicalWitness`). I29 scratch copies live under `scratchpad/c4a/stage`.

H16 deltas applied to the SX def: `0 < ε` kept; `εbar ≤ coneAccuracy` added (the only named cone
threshold; `epsW`, `windowFarAccuracy` are existential outputs of uncommitted/unbuilt bricks, so the
SX prover lane takes `min` with them inside its own `εbar`); `∃ Cx` moved before `∀ B`; the C3 output
is an independent input `∀ η₃, 0 < η₃ → OutputsOn η₃ → ∃ η, 0 < η ∧ η ≤ η₃ ∧ t₀ + η ≤ slab end ∧ …`.
Lower bounds `1 ≤ C1`, `1 ≤ C2`, `0 < τmin` kept as in the design: H16's `max 1 C` / `max 1 τmin`
relaxation is a proof device for the SX lane (monotone), and the leaf supplies these bounds anyway.

## 2026-09-26 entry 2 (delivered; all compiled read-only, zero output)

Files (new, uncommitted; paths under `Surgery/Topology/`):
- `SpatialCrossingContinuation.lean` (86 lines): `def SpatialCrossingContinuation` (SX) with the
  H16 deltas above. Compiled directly (`lake env lean`, lakefile options): rc=0, no output.
- `SpatialCanonicalContinuationCases.lean` (171 lines):
  `OrientedThreeStage.IncomingSlab.derivativeBoundBefore_of_derivativeBoundOn` (P0),
  `OrientedThreeStage.IncomingSlab.exists_spatialCanonicalWitness_of_canonicalOn` (case (A)),
  `def SpatialCanonicalContinuationWithAccuracy` (the I29 body of the leaf, verbatim),
  `spatialCanonicalContinuationWithAccuracy_of_spatialCrossing` (L; age split, `by_cases
  CapWindowPoint`, (B) = M5, (C) = SX; `C1s = max C1 (max Cw Cx)`,
  `C2s = max C2 (max (max Cw Cgrad) Cx)`, `Cs = 1`, `qs = qcan`, `q₄ = qx`, mins/maxes of the rest;
  `η` is SX's own `η` since SX now returns `η ≤ η₃`). Scratch module
  `C4A.SpatialCanonicalContinuationCases` over scratch `C4A.CapWindowSpatialCanonicalWitness` (M5)
  and `C4A.SpatialCrossingContinuation`: rc=0, no output.

Axioms (probe outside the tree, removed): P0, (A), L, M5, and the I29-form L and the I29 strong
assembly below: all `[propext, Classical.choice, Quot.sound]`.

Names: all five new public names unused elsewhere in the tree (grep).

I29 verified in scratch copies (`scratchpad/c4a/stage`, tree copies untouched):
- `C4A.SpatialCanonicalContinuation` (I29 applied) rc=0;
- `C4A.CanonicalNeighborhoodsThroughSurgeryStrong` (the 8-line `min εbar εs` change, over the
  working copy that already carries the foreign `SimplyConnectedSpace` binder diff) rc=0;
- `C4A.SpatialCanonicalContinuationCasesI29` (Cases with the WithAccuracy def deleted, L renamed
  `spatialCanonicalContinuation_of_spatialCrossing` and concluding the I29 `SpatialCanonicalContinuation`)
  rc=0. So the WithAccuracy body is definitionally the I29 body.

`SpatialCanonicalContinuationWithAccuracy → SpatialCanonicalContinuation` (current form): not
proved, not expected to hold. The current form demands, for every `ε ∈ (0, 1/11)`, a spatial
continuation from hypotheses at accuracy `ε`; WithAccuracy supplies it only for `ε ≤ εbar`. Neither
side is monotone in `ε` (witness accuracy appears in both hypotheses and conclusion), so an
`ε ∈ (εbar, 1/11)` instance cannot be reduced to an `ε' ≤ εbar` one. The converse is trivial
(`εbar := 1`).

Deferred merges: none (no private lemma copied; no committed file edited).

I29 edit text (for the acceptance lane; staged copies at `scratchpad/c4a/stage/*.lean`):
- `SpatialCanonicalContinuation.lean:145`: replace
  `  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 →` by
  `  ∃ εbar : ℝ, 0 < εbar ∧` / `  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar →`.
- `CanonicalNeighborhoodsThroughSurgeryStrong.lean:278–284`: after `obtain ⟨εbar, hεbar, hcont⟩ := hcont`
  insert `obtain ⟨εs, hεs, hspat⟩ := hspat`; `refine ⟨min εbar εs, lt_min hεbar hεs, ?_⟩`; feed
  `(hεbar'.trans (min_le_left _ _))` to `hcont B ε hB hε hε'` and
  `(hεbar'.trans (min_le_right _ _))` to `hspat B ε hB hε hε'` (before `C1 C2 τmin …`).
- In `SpatialCanonicalContinuationCases.lean`: delete `SpatialCanonicalContinuationWithAccuracy`,
  rename L to `spatialCanonicalContinuation_of_spatialCrossing`, conclusion
  `SpatialCanonicalContinuation P₀ g₀` (= stage file `SpatialCanonicalContinuationCasesI29.lean`).
- `PoincareEndgame.lean`: new leaf `spatialCrossingContinuation : SpatialCrossingContinuation P₀ g₀
  := by sorry`, and `spatialCanonicalContinuation … := spatialCanonicalContinuation_of_spatialCrossing
  P₀ g₀ (spatialCrossingContinuation P₀ g₀)`; register the two new modules (and M5) in the root.
