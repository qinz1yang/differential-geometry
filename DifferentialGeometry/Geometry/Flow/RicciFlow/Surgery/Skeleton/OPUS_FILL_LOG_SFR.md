# SFR — S bricks B5–B8: coarse+fine factory F* (2026-09-26)

Worktree `D:\differential-geometry-pc3` (branch `codex/pc-target-c-psf` @ 950618ee3). Paths relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/`. No git writes, no `lake build`.

## Progress
- 05:10 PDT start. Read AGENTS.md, NAMING, Skeleton/README, DESIGN_S_FACTORY, logs SFM/SB3/SB4, the chain
  files (HornFirstScalarLevel, BaseHornMetricEvent, HornCutoffRecord, PreparedHistoryCutoff,
  PoincareHornCutoffRecord), TerminalCorePresentationOfSpatiallyCanonical (A1), DiscardedSpatialClassification
  (A2), and `UniformDebitSurgeryStepStrong`.
- Precision audit of the chain (site S5). P's `ε` plays two roles: coarse (tolerances `ε ≤ eta` of the
  horn separation, collar matching, deep coordinates; `2ε < 1`) and fine (first-hit neck precision:
  `2ε ≤ δ`, `δ⁻¹+2 < (2ε)⁻¹`, `m+6 ≤ ⌊ε⁻¹⌋+1`, `⌊ε₀⁻¹⌋` order, backward-survival `2ε ≤ ηstar`,
  `mstar ≤ ⌊ε⁻¹⌋+1`). The collar matching `exists_horn_neck_collar_matching_of_deep_coordinates` is already
  precision-generic in the neck (`δ₀ ≤ ε`, window `δ⁻¹+1 < δ₀⁻¹`, output `neckBuffer δ₀`), and
  `exists_oriented_horn_neck_data_of_matching`/`exists_finite_oriented_neck_data_of_chosen_family` are generic
  in `δ`. So the fine copies are: R1 (:233, :425), BaseHornMetricEvent deep coordinates (:137), common-scale
  matching (:211; presentation mono'd to `2ε`, neck mono'd to `2εc`), reparametrized matching (:282), the
  family (:1220), first hit (:1380, :1463, :1555); then HornCutoffRecord :1161 → :2329 (+ :3090), then
  PreparedHistoryCutoff :241 → :464 → :640, then F*.
- Layout (three new files under `Contract/`, nothing existing edited):
  `HornFineCutNecks.lean` (FineCutNecks, R1, R2), `HornFineCutoffRecord.lean` (R3),
  `PoincareHornCutoffRecordOfFineCutNecks.lean` (R4, HEq transport, spatial discarded tolerance, F*).
- 05:35 File 1 `Contract/HornFineCutNecks.lean` compiles clean (42 s): `FineCutNecks`, R1 (+ reparametrized
  form), R2 private copies (deep coordinates, common-scale and reparametrized matching, family, first hit
  ×3). Compile method: read-only olean mirror `E:\sfr-mirror` of `E:\differential-geometry-pc3-lake\build\lib\lean`
  (real dirs along `…/Surgery/{Contract,Topology}`, junctions elsewhere, hard links for files); new oleans
  (`HornFineCutNecks`, SB4's `CompactComponentSpatialClassification`, `DiscardedSpatialClassification`)
  written into the mirror with `lean -o/-i`, LEAN_PATH = lake's with the project entry replaced,
  `LEAN_NUM_THREADS=2`. Existing oleans are never written (script refuses hard-linked targets).
- 06:00 File 2 `Contract/HornFineCutoffRecord.lean` compiles clean (6 min): private fine copy of :1161 and
  the public merge of :2329 + :3090. Pitfall: `PreparedCutoffEventGeometry` is a private structure; its fields
  cannot be read by dot notation from another module ("Field … is private"), but `open private
  PreparedCutoffEventGeometry.neck …` exposes the projections as functions. `open private orientedRotatedNeck`
  is ambiguous (also `IncomingBackwardNeck.orientedRotatedNeck`); the definition is unfolded in place.
- 06:35 File 3 `Contract/PoincareHornCutoffRecordOfFineCutNecks.lean` compiles clean (1.5 min): private fine
  copies of PreparedHistoryCutoff :241 and :464+:640 (merged; the merged proof first hit the 200000-heartbeat
  limit through three `nlinarith` calls that saw the larger context — replaced by explicit
  `mul_le_of_le_one_left`/`pow_le_pow_left₀`, no option), HEq transports of `SpatiallyCanonicalBefore` and
  `DerivativeBoundBefore`, the spatial sibling of the private discarded tolerance lemma (SB4 headline), F*.
  Next: rebuild all three with the Mathlib standard linter set, `#lint`, axioms.
- 06:55 Standard-set rebuild of all three files (`-Dweak.linter.mathlibStandardSet=true`, `lean -o` into the
  mirror): no output. `#lint in <module>` for each: 0 errors except `docBlame` on `FineCutNecks`
  (inapplicable per AGENTS.md). Axioms (scratch file importing the mirror oleans) of F*, the R3 public theorem,
  both R1 theorems and `exists_fine_neck_at_horn_first_scalar_level`: `[propext, Classical.choice, Quot.sound]`.
  Lines ≤ 100 (imports excepted); no comments, docstrings, sorry, nolint or budget options; only
  `set_option autoImplicit false`. Public names grepped unique. Not registered in the root aggregate.
  Line counts: 936 + 559 + 796 = 2291.

## Outcome: B5–B8 PROVED (sorry-free), with two deliberate deviations (below)

### (1) `FineCutNecks` (file 1, ns `…Surgery.Topology.TerminalCorePresentation`, design §2 (b) verbatim)
```
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)
def FineCutNecks (εc Qc : ℝ) : Prop :=
  ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (x : D.slab.terminalRegularOpen),
    x ∈ interior (range fun p : HalfNeckCylinder => P.horn c e p.1) →
    Qc ≤ metricScalarAt D.terminal.metric x →
    ∃ (δ : ℝ) (k : ℕ) (N : NormalizedNeck D.terminal.metric δ k),
      N.center = x ∧ δ ≤ εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ k
```
It is stated on the presentation (horn points are P's), as in the design, not on `D`.

### (2) R1–R5
- R1 (file 1, public): `exists_fine_neck_at_horn_first_scalar_level` (first hit via `FineCutNecks`);
  `exists_horn_first_scalar_level_inner_scalar_bound_tolerance_of_fineCutNecks` (← HornFirstScalarLevel:233)
  and `TerminalCorePresentation.exists_horn_first_scalar_level_reparametrized_scalar_bound_tolerance_of_fineCutNecks`
  (← :425). New binders after `ε ≤ eta`: `∀ {εc Qc}, 0 < εc → εc ≤ ε → P.FineCutNecks εc Qc →`, and `Qc ≤ Q`
  after the level hypothesis; conclusion `δ ≤ εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ k`. The in-proof coarse `horn_spatial_neck`
  use (the `3Q` barrier at other points) is unchanged.
- R2 (file 1, private): `exists_common_deep_coordinates_of_fine_neck_family` (← :137; now depends only on
  `εc`), `exists_common_scale_horn_matching_of_fine_neck_family` (← :211: presentation mono'd to `2ε`, neck to
  `2εc`, collar matching at the neck's own precision), `exists_reparametrized_horn_matching_of_fine_neck_family`
  (← :282), `exists_fine_neck_family_first_scalar_level_reparametrized_bound` (← :1220),
  `exists_first_hit_reparametrized_horn_matching_of_fineCutNecks` (← :1380),
  `exists_first_hit_oriented_horn_necks_of_fineCutNecks` (← :1463),
  `exists_finite_first_hit_oriented_horn_neck_data_of_fineCutNecks` (← :1555). Fine hypotheses
  `2 * εc ≤ δ`, `δ⁻¹ + 2 < (2 * εc)⁻¹`, `m + 6 ≤ ⌊εc⁻¹⌋₊ + 1`; conclusion
  `δOriginal j ≤ 2 * εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ kOriginal j`. The coarse `ε ≤ eta` stays on P.
- R3 (file 2): private `exists_prepared_horn_cutoff_event_with_original_neck_bounds_of_fineCutNecks`
  (← HornCutoffRecord:1161; head `∃ c _ A hA Kreset, 3 ≤ Kreset ∧ ∃ εcoarse, 0 < εcoarse ∧ ∀ Dcap … ∃ δ … ∃ ε₀,
  ∀ P, ε ≤ εcoarse → ∀ {εc Qc}, 0 < εc → εc ≤ ε → εc ≤ ε₀ → P.FineCutNecks εc Qc → ∃ coreBound, … ∀ Q, … →
  … → Qc ≤ Q → …`); public `exists_horn_cutoff_history_extension_with_canonical_windows_of_fineCutNecks`
  (merge of :2329 and :3090; statement = :3090 with the same substitution and `∃ εcoarse` after
  `4 ≤ recenterConstant`).
- R4 (file 3, private): `exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks`
  (← PreparedHistoryCutoff:241; `εc ≤ ε₀` with `ε₀ = min εfactory (min (ηstar/2) ((mstar+1)⁻¹))` feeds
  `2εc ≤ ηstar`, `mstar ≤ ⌊εc⁻¹⌋₊+1`; `q0` stays deferred after `ηstar mstar Λq`),
  `exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks` (merge of :464 and :640; the fine
  hypothesis is `P.FineCutNecks εc Q` at the chosen `Q`, placed before `Λ ≤ Λmax → coreFloor ≤ P.coreRadius`).
- R5 = F* (file 3, public). Statement head (conclusion = the existing factory's with `ε₀ ↦ εP` in P's type and
  `2 * εcut`, `⌊εcut⁻¹⌋₊` in the original-neck clause; `Λq * max q0 1 ≤ Q` dropped):
```
open OneStepIncoming in
theorem exists_horn_cutoff_record_with_uniform_volume_debit_of_spatiallyCanonical_of_fineCutNecks
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εP εbar : ℝ, 0 < εP ∧ 0 < εbar ∧ εbar < 1 / 11 ∧
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∃ δ εcut : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < εcut ∧ εcut ≤ εP ∧
    ∀ C1 C2 : ℝ, 1 ≤ C2 →
    ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
    ∀ qcan originalCoreFloor protectedFloor Kfine : ℝ,
      0 < qcan → 0 < originalCoreFloor → 0 < protectedFloor → 0 ≤ Kfine →
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ H initial, H.time last = H.horizon → ∀ ρold, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ s G L hsing stepParameters, G.flow.base.metric (H.time last) = H.initialMetric last →
    let D : OneStepIncoming := { … parameters := stepParameters }
    (history derivative clause above qcan) → (G derivative clause above qcan) →
    originalCoreFloor ≤ D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime →
    protectedFloor ≤ D.parameters.protectedRadius D.endTime →
    G.SpatiallyCanonicalBefore εbar C1 C2 qcan s →
    (∀ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t)
      (P : TerminalCorePresentation (D.withNeckRadius ρ hρ) εP Λ),
      Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Q → P.FineCutNecks εcut Q) →
    ∃ ρ hρ, … ∃ P : TerminalCorePresentation D' εP Λ, … ∃ Qout E …, (existing conclusion)
```
  Inside: `εP := min εcoarse etaDisc`; `εbar := εcan(εP)` from A1 (`104000·εbar ≤ εP`, so `εbar ≤ etaDisc`);
  `η := min ηrecord εbar` (record precision `≤ εbar` for A2); `εcut := min εP ε₀`; A1 at threshold `C·qcan`;
  `Qlower := max (C2²·radiusFloor⁻²) (Kfine·max (Λ·radiusFloor⁻²) (max qcan 1))`, so the F* premise holds
  for the P it builds. Discarded classification: SB4's headline through the new private
  `exists_poincareStandardDiscarded_of_retainedEvent_heq_of_spatiallyCanonical` at `eps := εbar`.

### (3) HEq transport and the discarded swap (file 3, private)
`spatiallyCanonicalBefore_of_incoming_heq` and `derivativeBoundBefore_of_incoming_heq`
(`P = Q → a = b → s = t → HEq G F → F.… t → G.… s`, mirror of `derivative_bound_of_incoming_heq`), used in
the spatial sibling of `exists_poincareStandardDiscarded_of_retainedEvent_heq_tolerance` (it calls
`GeometricCutoffRecord.exists_poincareStandardDiscarded_tolerance_of_spatiallyCanonical`).
`PoincareHornCutoffRecord.lean` was not edited (its privates are reached by `open private`).

### Deviations (reasons)
- F* does not take `κ`, noncollapsing, or the long-slab hypothesis `2θ ≤ Q(s−a)`: F* consumes
  `FineCutNecks` directly, and no proof step of F* reads them; adding them would be unused binders. They are
  hypotheses of the supplier B12 and enter when F* is composed with B12 (below). To make that composition
  possible without B12 in hand, F* takes the supplier's constant `Kfine` before `∃ Q` and guarantees
  `Kfine·max(Λ·r⁻², max qcan 1) ≤ Q` for its presentation.
- `ε̄` is kept existential (no `hornCoarseAccuracy` def); `εP` is exported too, because the fine
  hypothesis names the presentation precision.

## (5) Remaining gap F* → `UniformDebitSurgeryStepStrong P₀ g₀` (S), precise
S (`Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean:124`, HEAD a161fc07e):
`∀ B εbar, 0 < B → 0 < εbar → ∃ Λ, 0 < Λ ∧ ∀ Ctime, ∃ ε, 0 < ε ∧ ε < 1/11 ∧ ε ≤ εbar ∧
 ∀ C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap mcap Cgrad κ a₀, (positivity) → ∃ p₀ δbound ρbound v, … ∧
 ∀ H, InitialIdentification → ∀ hend, H.horizon < B → H.hasCanonicalCutoffRecords p₀ δbound ρbound →
 (history derivative) → (history gradient) → (history CanonicalBefore ε C1 C2 qcan τmin) →
 (history SpatiallyCanonicalBefore ε C1s C2s qcan) → (Hamilton–Ivey a₀) → H.NoncollapsedBefore κ ε … →
 ∀ s G, s ≤ B → ∀ hG, G.SingularEndpoint → (G derivative) → G.GradientBoundBefore Cgrad qcan s →
 (G canonical, age ≥ τmin) → G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
 (∀ t₀ ∈ Ioo (H.time last) s, H.TerminalNoncollapsedBefore hend G hG κ ε t₀) →
 ∃ Q E hinit q, E.incoming = G ∧ (H.appendEvent …).hasCanonicalCutoffRecords p₀ δbound ρbound ∧ … ∧
 Nonempty (GeometricCutoffRecord …) ∧ boundaryFrameReversing ∧ poincareStandardDiscarded ∧ (volume debit v)`.
Instantiation per design §5 (`Λ := recenterConstant`, `Dbig := max Dcap (Dtrace+1)`, `C1 C2 := C1s C2s`,
constant `stepParameters`, floors `δ·ρbound`) plus:
- G1 (B12, long slab) must supply F*'s fine premise:
  `∀ {εc} (0 < εc) (εc < 1/2) {κ} (0 < κ) {ρ} (0 < ρ) {Φ} (AdmissiblePinchingFunction Φ) (C1 C2 : ℝ) (1 ≤ C2)
   (Ctime : ℝ≥0), ∃ K θ : ℝ, 1 ≤ K ∧ 0 < θ ∧ ∀ (D : OneStepIncoming) {Λ}
   (P : TerminalCorePresentation D εP Λ) (q Qc : ℝ), 0 < q → D.slab.DerivativeBoundBefore Ctime q D.endTime →
   PhiAlmostNonnegative D.slab.flow (Ico D.startTime D.endTime) Φ →
   D.slab.SpatiallyCanonicalBefore εbar C1 C2 q D.endTime → (κ-noncollapsing near the end, radius ≤ ρ) →
   K * max (Λ * (P.coreRadius ^ 2)⁻¹) (max q 1) ≤ Qc → 2 * θ ≤ Qc * (D.endTime - D.startTime) →
   P.FineCutNecks εc Qc`,
  with `εP, εbar` F*'s constants. B14 applies it at `εc := εcut`, `q := qcan`, `Qc := Q` and passes
  `Kfine := K`. The κ clause must be derivable from S's `H.TerminalNoncollapsedBefore hend G hG κ ε t₀`
  (HistoryNoncollapsingToSlab:95).
- G2 (B13): the same conclusion without `2 * θ ≤ Qc * (D.endTime - D.startTime)` (history window through
  `RegularCrossing`, design §0.1). Until B13, S follows only on long terminal slabs.
- G3 (new, small): ε-monotonicity of spatial witnesses. S picks `ε ≤ εbar` for an arbitrary input `εbar`,
  while F* needs `G.SpatiallyCanonicalBefore εbar_F* …` at its fixed constant; with `ε := min εbar εbar_F*`
  one needs
  `theorem OrientedThreeStage.IncomingSlab.spatiallyCanonicalBefore_mono_eps {ε ε' C1 C2 q t : ℝ}
     (hε : ε ≤ ε') (hε' : ε' < 1 / 11) : G.SpatiallyCanonicalBefore ε C1 C2 q t →
     G.SpatiallyCanonicalBefore ε' C1 C2 q t`
  (spatial analogue of `CanonicalWitness.mono_eps` + `cap_neck_chart_mono_tolerances`; `SpatialNeck.mono`
  exists in `Geometry/Neck/SpatialTolerance.lean`; chain, local-cap and round-comparison monotonicity are
  missing).
- G4 (B14 bookkeeping, HANDOFF_S steps 3–4): records bound `δbound := min δmax δold` vs F*'s `δold`
  (input monotone in the bound; output: F* concludes `K.hasCanonicalCutoffRecords p₀ δold ρold` under
  `ηrecord ≤ δold`, S needs `… p₀ δbound ρbound`), `ηrecord := min δmax (min δold εbar)`, `p₀` assembly, and
  the event/record repackaging into S's `∃ Q E hinit q` form.
S's `CanonicalBefore`, `Cgrad`, `a₀`, `NoncollapsedBefore` are not read by F* (design §0.3).

## Compile method (read-only, no `lake build`)
Mirror `E:\sfr-mirror` (see 05:35); per file `lean -o <mirror>/…olean -i … [-Dweak.linter.mathlibStandardSet=true]`
with LEAN_PATH = lake's path with `D:\differential-geometry-pc3\.lake\build\lib\lean` replaced by the mirror,
`LEAN_NUM_THREADS=2`, dependency order: SB4's CompactComponentSpatialClassification and
DiscardedSpatialClassification (uncommitted at the time; committed since in a161fc07e, unchanged),
HornFineCutNecks (≈1 min), HornFineCutoffRecord (≈6 min), PoincareHornCutoffRecordOfFineCutNecks (≈1.5 min):
all exit 0 with no output. Mirror and probes removed afterwards (junctions unlinked first).
