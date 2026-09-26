# OPUS_FILL_LOG_SFM — factory bricks B1 (reorder) + B2 (derivative clause, entry 17)

Worktree `D:\differential-geometry-pc3`, base 06a347488. Paths relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/`. No git writes, no `lake build`.

## 2026-09-26 start — site audit (grep `time_derivative`)

Reads of `CanonicalWitness.time_derivative` from a *hypothesis* (not from the slab's own
`exists_all_point_canonical_neighborhoods`, which is intrinsic and not a factory input):

- `Topology/TerminalCanonicalCapture:116` `exists_compact_containing_canonical_domains` — no consumers.
- `Topology/TerminalNeckNormalization:518` `eventually_normalizedNeck_of_canonical_neighborhoods` —
  only consumer `TerminalSphericalBarrier:38` supplies intrinsic witnesses; not on the factory path.
- `Topology/DiscardedCanonicalCoverage:74` `eventually_canonical_on_discarded_core` — only consumer
  `:109` is intrinsic; not on the factory path.
- `Topology/DiscardedCanonicalCoverage:149`
  `exists_late_canonical_on_discarded_core_with_cap_neck_charts_of_canonical_neighborhoods` —
  factory path (S4: discarded classification).
- `Topology/TerminalComponentClassification:94`
  `exists_component_poincareStandard_tolerance_of_canonical_neighborhoods` — factory path (S4).
- `TerminalScalarSublevel:25`, `TerminalCapCapture:182,304`, `TerminalCapNormalization:69`,
  `TerminalComponentClassification:40` read intrinsic slab witnesses: no factory dependence.
- Contract/ (factory chain files) has no `time_derivative` read. The geometry branch of the factory
  (`hgeo` → `TerminalCorePresentationExistence` → `TerminalCutoffScale` → …) reads no
  `time_derivative` from its hypothesis (every read in its closure is one of the above).

So the factory's `time_derivative` dependence is exactly the two S4 reads, both on theorems that
also read other witness fields (conclusion re-exports witnesses / alternatives): witness hypotheses
stay, the derivative is separated into its own clause.
`DerivativeBoundBefore` lives in `Topology/CanonicalNeighborhoodInduction.lean`, which is not in the
factory's import closure; the clause is stated unfolded (definitionally
`G.DerivativeBoundBefore Ctime q s`).

## B2 — derivative clause separated (entry 17)

Clause shape used everywhere (unfolded `DerivativeBoundBefore Ctime q s` on the slab concerned):
`∀ x, ∀ t ∈ Ioo a s, q < S.scalar t x → |derivWithin (fun v => S.scalar v x) (Iic t) t| ≤ Ctime * S.scalar t x ^ 2`.
Threshold/time: every site already used the witness hypothesis on `Ioo a s` above the same `q`, so no
extra `qcan < R` / time-range facts were needed.

1. `Topology/DiscardedCanonicalCoverage.lean`
   `GeometricCutoffRecord.exists_late_canonical_on_discarded_core_with_cap_neck_charts_of_canonical_neighborhoods`
   - before: `{eps C1 C2 Q : ℝ} (hQ : 0 < Q) (hC2 : 0 ≤ C2) (hcanonical : …) {Phi} (hPhi) (hpinch) (hprotected)`
   - after: `{eps C1 C2 Q : ℝ} {Ctime : ℝ≥0} (hQ : 0 < Q) (hcanonical : …) (hbound : clause above Q on (H.event i).incoming) {Phi} (hPhi) (hpinch) (hprotected)`
   Same change on the wrapper `exists_late_canonical_on_discarded_core_with_cap_neck_charts`
   (no consumers). Witness hypothesis kept: the conclusion re-exports witnesses.
2. `Topology/TerminalComponentClassification.lean`
   `IncomingSlab.exists_component_poincareStandard_tolerance_of_canonical_neighborhoods`:
   after the witness clause, inserted `∀ Ctime : ℝ≥0, (clause above q on G) →`; the internal
   `hbound` built from `W.time_derivative` (constant `max C2 0`) is deleted. Witnesses kept (the
   compact classification reads the full alternative).
3. `Topology/DiscardedComponentClassification.lean`: private
   `exists_isPoincareStandard_discarded_boundary_tolerance` and public
   `GeometricCutoffRecord.exists_poincareStandardDiscarded_tolerance_of_canonical_neighborhoods`:
   after the witness clause, inserted `∀ Ctime : ℝ≥0, (clause above Q / q on (H.event i).incoming) →`.
   Consumer `exists_poincareStandardDiscarded_cutting_scale_of_incoming` supplies it from the
   slab's own intrinsic witnesses (`(hcan …).choose.time_derivative`, constant `⟨C, _⟩`); its
   statement is unchanged. `open scoped … NNReal` added for `ℝ≥0`.
4. `Topology/TerminalCanonicalCapture.lean` `TerminalLimitMetric.exists_compact_containing_canonical_domains`
   (design S1 :108/:116, no consumers): added `{Ctime : ℝ≥0}` and
   `(hbound : clause above q on G)` after `hcanonical`; internal read deleted.
5. `Contract/PoincareHornCutoffRecord.lean`: new private `derivative_bound_of_incoming_heq`
   (HEq transport, same pattern as `canonical_neighborhoods_of_incoming_heq`); the private
   `exists_poincareStandardDiscarded_of_retainedEvent_heq_tolerance` takes
   `∀ Ctime : ℝ≥0, (clause above q on E.incoming) →` after its witness clause.
   Factory: new hypothesis, placed right before the witness hypothesis,
   ```
   (∀ y, ∀ t ∈ Ioo D.startTime D.endTime, qcan < D.slab.flow.scalar t y →
     |derivWithin (fun v => D.slab.flow.scalar v y) (Iic t) t| ≤
       Ctime * D.slab.flow.scalar t y ^ 2) →
   ```
   i.e. `D.slab.DerivativeBoundBefore Ctime qcan D.endTime` (= `G.…`, same `Ctime` as the
   history clauses). It feeds the discarded classification through `hG : E.incoming = D'.slab`.

Not changed (intrinsic-only reads, not factory inputs): `TerminalNeckNormalization:518`
(`eventually_normalizedNeck_of_canonical_neighborhoods`; after the swap it would duplicate
`eventually_normalizedNeck_of_strongNecks_of_scalar_control`), `DiscardedCanonicalCoverage:74`,
`TerminalScalarSublevel:25`, `TerminalCapCapture:182,304`, `TerminalCapNormalization:69`,
`TerminalComponentClassification:40`. After this change the factory reads no
`CanonicalWitness.time_derivative` from its witness hypothesis.

## B1 — universal `fixed`, `recenterConstant` first

Before (all six theorems):
```
theorem X (P₀) (g₀) (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0) (hmargin : Dtrace + 1 ≤ Dbig)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000) (hr : transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < Dtrace) :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εold δold : ℝ, …
```
After:
```
theorem X (P₀) (g₀) :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, …   (rest verbatim)
```
for `PreparedHistoryCutoff`: `exists_horn_cutoff_record_at_scale_of_initialIdentification` (:464),
`…_with_uniform_volume_debit_above_scale_of_initialIdentification_and_core_radius_lower_bound` (:639),
`…_with_uniform_volume_debit_of_initialIdentification_and_core_radius_lower_bound` (:793),
`…_of_initialIdentification_and_canonical_neighborhoods_and_canonical_records` (:931), and
`PoincareHornCutoffRecord` factory (:461). `exists_horn_cutoff_record_at_scale_of_prepared_history`
(:241, no `P₀ g₀`): `∃ fixed rc, 4 ≤ rc ∧ ∀ (Dtrace r tol a₀ : ℝ) (Ctime : ℝ≥0), 0 < a₀ → 0 < tol →
tol ≤ 1/1000 → hr → hfit → ∃ εold δold …`. `fixed` comes from the input-free
`exists_uniform_horn_cutoff_history_extension_at_scale_with_original_neck_bounds_and_canonical_windows`.
The old shape is derivable by instantiation (`obtain ⟨fixed, c, hc, h⟩ := X P₀ g₀; h Dtrace …`); no
corollary added (no consumer outside the chain; all in-chain consumers updated).

`Dbig := max Dcap (Dtrace + 1)`: the factory keeps `Dbig` universal with `Dtrace + 1 ≤ Dbig`, so
the design's choice is made at S (`le_max_right`); nothing to change in the factory.
`ηrecord ≤ ε̄`: no named `ε̄` exists yet (it is B8's `ε̄`). The factory already enforces record
precision `≤ epsTop = min eta (1/22)` internally (`hfactory … (min ηrecord epsTop)`, `hδTop`), which is
the S4 requirement `∀ j, Record.delta j ≤ eps`. No constant introduced.

## Compile (read-only, no lake build)

Mirror `E:\sfm-mirror\lean` of `E:\differential-geometry-pc3-lake\build\lib\lean` (the build dir
behind the `.lake` junction): real directories along `…/Surgery/{Topology,Contract}`, junctions for
all other subdirectories, hard links for all other files; the six edited modules' links deleted and
rewritten by `lean -o/-i` with `LEAN_PATH` = lake's path with the project entry replaced by the
mirror, `LEAN_NUM_THREADS=2`, dependency order:
TerminalCanonicalCapture (24 s), DiscardedCanonicalCoverage (29 s), TerminalComponentClassification
(31 s), DiscardedComponentClassification (29 s), PreparedHistoryCutoff (94 s),
PoincareHornCutoffRecord (78 s): all exit 0, no output (no errors, no warnings).
Axioms (scratch file importing the mirror oleans): the factory, `…_canonical_records`,
`…_of_prepared_history`, `exists_poincareStandardDiscarded_tolerance_of_canonical_neighborhoods`,
`exists_poincareStandardDiscarded_cutting_scale`, `exists_late_canonical_on_discarded_core_with_cap_neck_charts`,
`exists_component_poincareStandard_tolerance_of_canonical_neighborhoods`,
`exists_compact_containing_canonical_domains`: `[propext, Classical.choice, Quot.sound]`.
Not run: the 13-linter audit and the downstream rebuild (lead). Diff: 6 files, +124 −81.

Mirror removed afterwards (links and junctions unlinked, targets untouched; real build oleans
unchanged, e.g. PoincareHornCutoffRecord.olean still 03:27).
