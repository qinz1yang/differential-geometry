# Leaf S — `UniformDebitSurgeryStep`

Statement: `Surgery/Topology/CanonicalNeighborhoodsThroughSurgery.lean`, `def UniformDebitSurgeryStep`.
Leaf: `Surgery/Skeleton/PoincareEndgame.lean`, `uniformDebitSurgeryStep`. Ledger: `Surgery/FREE_INPUTS.md`.

## Binder order after the interface revision (entry 28, accepted 2026-09-26)

S takes the accuracy ceiling `εbar` of C and returns `ε ≤ εbar`; the cap parameters, record
bounds and debit are chosen after every constant of C
(`Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean:124`). The factory contracts are
threshold-ordered (`∃ δ ε₀ Λq …, 0 < Λq ∧ ∀ q0, 0 < q0 → …` with `Λq * max q0 1 ≤ Q`, on
`exists_threshold_uniform_selected_neck_append_backward`), so `εcan` no longer depends on `q0`.
The class clause `p₀.recenterConstant * δbound ≤ 1 / 2` is derived from S's output
`p₀.recenterConstant ≤ Λ` inside C's assembly; it adds nothing to S's statement.

```lean
def UniformDebitSurgeryStepStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ (B εbar : ℝ), 0 < B → 0 < εbar →
  ∃ Λ : ℝ, 0 < Λ ∧
  ∀ Ctime : ℝ≥0,
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ ε ≤ εbar ∧
  ∀ (C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Cgrad : ℝ≥0) (κ a₀ : ℝ),
    1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < τmin → 0 < δmax → 0 < ρmax →
    0 < εcap → 0 < Dcap → 0 < κ → 0 < a₀ →
  ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
    p₀.modelAccuracy ≤ εcap ∧ Dcap ≤ p₀.modelRadius ∧ mcap ≤ p₀.modelOrder ∧
    0 < δbound ∧ δbound ≤ δmax ∧ 0 < ρbound ∧ ρbound ≤ ρmax ∧ p₀.recenterConstant ≤ Λ ∧
    0 < v ∧
    ...
```

## What it says

Given a horizon `B`, choose an accuracy `ε < 1/11` (the accuracy of the canonical neighbourhoods
the cutoff will use; it may depend on `B` only). Then, given canonical constants `C1 C2`, a
threshold `qcan`, a derivative constant `Ctime` and admissibility bounds `δmax ρmax εcap` (all
chosen at that accuracy by the canonical-neighbourhood side, leaf C), produce once: cap parameters
`p₀` with `p₀.modelAccuracy ≤ εcap`, record bounds `δbound ≤ δmax`, `ρbound ≤ ρmax`, and one debit
`v > 0`. Then, for every history `H` in the class
`H.hasCanonicalCutoffRecords p₀ δbound ρbound` (initial identification, `time last = horizon < B`)
whose slabs satisfy `|∂ₜR| ≤ Ctime R²` above `qcan`, and every singular incoming slab `G` from its
end with `s ≤ B`, the same derivative bound and canonical witnesses
`CanonicalWitness G.flow ε C1 C2 x t` with `capTubeHasNeckChart ε` above `qcan`: return the next
`RetainedCoreEvent` with `E.incoming = G`, class closure for `H.appendEvent`, a
`GeometricCutoffRecord` at the last index whose fixed fields equal `p₀`'s,
`boundaryFrameReversing`, `poincareStandardDiscarded`, and the debit inequality with `v`.

## Base and porting cost (measured 2026-09-25)

This lane is based on the `codex/wt17-pc-build-warning` lineage (22a24821b; the branch has since
advanced 30 commits: cap survival, cap action bounds, standard comparison). The factory below lives
only on `origin/codex/pc-sorry-free`. Its import closure there has 10,682 modules: 10,584 identical
to wt17, 12 new files, 55 files changed only on pc-sorry-free (clean cherry-picks) and **31 files
changed on both sides since the merge base 8e09bcaf0** (`EventData.lean`, `HistoryAction.lean`,
`HistorySurvivor*`, `CapWindow*`, `StandardCap/Window*`, `Metric/Convergence/Metric/Evaluation.lean`,
`Topology/FirstExit.lean`, …). A partial cherry-pick is therefore not viable: either the two lines
are merged by their owners, or S is re-derived on the wt17 lineage with wt17's own cap-survival and
history machinery, using the pc-sorry-free factory as the route.

## What exists (branch `origin/codex/pc-sorry-free` @ 6d15b3ed9, not on this base)

`Contract/PoincareHornCutoffRecord.lean:461`
`exists_horn_cutoff_record_with_uniform_volume_debit_and_poincareStandardDiscarded_of_canonical_neighborhoods`
proves every conclusion of S: event, `Record` with `Record.delta = fun _ => δ`, all necks at scale
`Q`, canonical windows, `E.poincareStandardDiscarded`, `K.hasCanonicalCutoffRecords p₀ δold ρold`
(the closure, under `ηrecord ≤ δold` and `stepParameters.neckRadius s ≤ ρold`), the debit
`#cuts · v` with `v = Q^(-3/2)` and `Q` chosen before `H`, `boundaryFrameReversing`. The event is
returned as `Eappend : MetricCutCapEvent (H.stage last) Qout (H.time last) s` with
`K = H.appendEvent Eappend.incoming.lt (Eappend.toRetainedCoreEvent hOldAppend) hInitial`, so the
`RetainedCoreEvent` of S is `Eappend.toRetainedCoreEvent hOldAppend`; its `.incoming`, `.terminal`,
`.outputMetric`, `.transition` are the projections of `Eappend` (`RetainedCoreMetricEvent.lean:64`);
`E.incoming = D'.slab` and `(D.withNeckRadius ρ hρ).slab = D.slab` (`Contract/TerminalCutoffScale.lean:21`)
give `E.incoming = G`; `poincareStandardDiscarded` reads only `.discarded`.

## The gap: binder order

The factory takes `Ctime` first, then `∀ m accuracy ηrecord q0`, and only then produces
`∃ δ ε₀ Qmin, ∃ εcan …, ∀ C1 C2, ∃ C Λ, ∀ qcan floors, ∃ Q v, ∀ p₀ H …`. Its canonical-neighbourhood
hypothesis is at the *output* accuracy `εcan` and its derivative hypothesis is above the *input*
threshold `q0`, with the cap accuracy `accuracy` also an input. S needs the accuracy `ε` first: it
may be chosen freely for each `B`, but before `C1 C2 qcan Ctime δmax ρmax εcap` are known, whereas
`εcan` of the factory depends on `q0` and `accuracy`.

Where the dependence is created: `Contract/PreparedHistoryCutoff.lean:237`
(`exists_horn_cutoff_record_at_scale_of_prepared_history`) sets
`ε₀ := min εfactory (min (ηstar / 2) ((mstar + 1)⁻¹))` with `ηstar mstar Qmin` from
`exists_uniform_selected_neck_retained_append_backward … q0 …`, and that theorem
(`Topology/ProspectiveNeckSurvival.lean:3444`, private base at `:3322`) chooses
`ηstar mstar Qmin` by contradiction: a counterexample sequence with `η_n → 0`, `m_n → ∞`,
`scale_n → ∞` for a fixed `q0` is refuted by the subsequence lemma
`exists_subsequence_selected_neck_append_backward`. So `ηstar` is formally a function of `q0`
(and of `accuracy` through `εfactory`), and no reordering of the statements alone recovers S.

## Proof plan

1. Show that the derivative threshold enters the backward survival only through the minimal
   scale: restate the subsequence lemma and `:3322` so that `ηstar, mstar` are produced before
   `q0` and only `Qmin` after it (Perelman: the precision needed for a δ-neck to survive
   backward is a function of `δ, tol, r, D`, while the curvature scale at which the derivative
   bound is used is `≳ Q`). If the subsequence lemma cannot take a sequence `q0_n`, prove a
   monotonicity lemma: the conclusion for `q0` implies the conclusion for every `q0' ≥ q0`
   (the derivative hypothesis above `q0'` is weaker), and choose `q0 := qcan` with `Qmin` above it.
2. Likewise separate `accuracy` from `εfactory` in
   `exists_uniform_horn_cutoff_history_extension_at_scale_with_original_neck_bounds_and_canonical_windows`,
   or prove that CN at accuracy `εcan` near a cap of accuracy `accuracy ≤ εcap(εcan)` follows from
   the standard-cap comparison; then choose `accuracy` after `εcan` by running the factory twice
   is **not** valid (the second run may change `εcan`), so the separation has to be in the statement.
3. With the constants in Perelman's order, instantiate: `ε := εcan` once it no longer depends on
   `q0` and `accuracy`; `Ctime` from C; `m := ⌈tol⁻¹⌉₊ + 2`, `accuracy := min εold εcap`,
   `ηrecord := min δold δmax`, `q0 := qcan`; `C1 C2` from C; `qcan` from C; the step floors are
   internal to the proof (they fix `Q`, hence `v = Q^(-3/2)`); obtain `Q v`;
   `p₀ := ⟨fixed, recenterConstant, m, accuracy, Dbig, …⟩` with constant time-dependent fields;
   `δbound := min δold δmax`, `ρbound := min ρ_step ρmax`.
4. Bookkeeping: `hasCanonicalCutoffRecords_appendEvent` (`Topology/CanonicalCapWindows.lean:135`)
   for the closure at `(δbound, ρbound)`; `Fin.ext` on `i.val = H.eventCount`; `cases eq_of_heq`
   on `HEq Eappend E`; transport of `Kvol` along `E.incoming = D'.slab` by generalising the slab.

## Acceptance

No `sorry`, no `axiom`, no `nolint`, no heartbeat overrides. Build the changed modules and every
module depending on them; `#print axioms` of `uniformDebitSurgeryStep` must be
`propext`, `Classical.choice`, `Quot.sound`; the 13-linter audit (`docBlame`, `docBlameThm`
excluded) on all changed modules; then move the theorem out of `Skeleton/` into
`Surgery/Topology/CanonicalNeighborhoodsThroughSurgery.lean` (or a producer module next to it),
register in the root aggregate, update `Surgery/FREE_INPUTS.md` in the same commit.

## Update 2026-09-25 (after the external review and Lane D)

* The interface now passes `τmin`, `Dcap` and `mcap` from C to S: S must choose `p₀` with
  `Dcap ≤ p₀.modelRadius` and `mcap ≤ p₀.modelOrder` (the factory takes `Dbig` and the model order
  as free inputs, so this is a choice, not an obstacle), and it receives the canonical-neighbourhood
  hypothesis only at points with `τmin ≤ R · (t − a)`. The factory's hypothesis
  `(∀ x t, t ∈ Ioo D.startTime D.endTime → qcan < R → ∃ W …)` has the old unrestricted shape and is
  unsatisfiable on any slab that follows a cut (fresh cap points have no `CanonicalWitness`); when
  the chain is ported it must be weakened to the age-restricted form, and the proof checked to use
  canonical neighbourhoods only at points with `R (t − a) ≥ τmin` (the horn near the singular time
  satisfies this for large `R`).
* The base-and-porting paragraph above is superseded by the measurement of 2026-09-25 afternoon:
  the five factory commits `c0f94726d a23551e62 e556f139e 95fb763bb 4fe90864a` cherry-pick cleanly
  onto this lineage (every file they touch is either new or identical to ours at their parent); the
  transitive need beyond that is 6 modules absent here, 31 changed only on `pc-sorry-free` and 2
  changed on both sides (`HistoryAction`, `HistorySurvivorIncoming`). Port bottom-up, compiling.
* **Age threshold versus the factory (second review FIX 3; third review, 2026-09-26,
  `consult/C-debit-step-review-digest.md`).** The earlier repair "cut at `h/√(C·Ctime·τmin)`" is
  RETRACTED: caps glued at scale `h'` have curvature `≈ h'⁻²`, the ratio is scale invariant. The
  real state: (i) the factory consumes canonical neighbourhoods at accuracy `≤ δ/208000`, finer
  than the record precision, so no binder order connects it to S; the missing brick is Perelman II
  4.3 / KL 71 (deep-horn neck improvement, queue entry 14), and the factory must be split into a
  coarse terminal decomposition at a fixed `ε̄` plus fine cutting necks; (ii) its terminal
  classification uses witnesses at points of terminal curvature above a fixed threshold `L` at
  times near `s`, whose normalized age `≈ L(s − a)` is not bounded below on short slabs, and such
  young points need not lie in cap regions (counterexample: a round `S³` component dying shortly
  after an event elsewhere); they do carry the `round`/`positive`/spatial alternatives, so S must
  consume an AGE-FREE SPATIAL canonical clause (`SpatialCanonicalWitness`, queue entry 13) beside the
  age-restricted strong witnesses, and the time derivative from the separate derivative clause;
  (iii) `q₀` must be deferred by a variable-threshold sequence version of
  `ProspectiveNeckSurvival` (`q₀ₙ/Qₙ → 0`, entry 16), `Ctime` chosen before `ε`; `m`, `accuracy`,
  `ηrecord`, `Dcap` are genuinely tied to the cut precision. S is restated
  `∀ B Ctime, ∃ ε, ∀ C's constants and κ, ∃ p₀ δbound ρbound v, …` with the noncollapsing input as
  `TerminalNoncollapsedBefore` on the slab `G` attached to `H`.
* The reorder concerns more than `q0`: `Ctime`, `m`, `accuracy` and `ηrecord` also precede `εcan`
  in the factory; `Ctime` is dimensionless and cannot be absorbed by a large scale. Record for each
  input whether its dependence is deferred to `Qmin` or removed by a uniform derivative estimate.
  "C holds for every ε" does not by itself uncouple a factory whose cutting accuracy depends on the
  cap accuracy; the honest alternative, if the reorder fails, is a joint compatibility statement for
  each horizon (one tuple `ε C1 C2 qcan τmin Ctime p₀ δbound ρbound v` with the class closed under the
  step), which the assembly can consume as well.

## Update 2026-09-26 (factory derivative clause and binder order; lane SFM, accepted by ACC4)

The factory `exists_horn_cutoff_record_with_uniform_volume_debit_and_poincareStandardDiscarded_of_canonical_neighborhoods`
(`Contract/PoincareHornCutoffRecord.lean`) now reads no `CanonicalWitness.time_derivative`: it takes
the derivative clause as its own hypothesis, placed right before the witness hypothesis,
`(∀ y, ∀ t ∈ Ioo D.startTime D.endTime, qcan < D.slab.flow.scalar t y → |derivWithin (fun v =>
D.slab.flow.scalar v y) (Iic t) t| ≤ Ctime * D.slab.flow.scalar t y ^ 2) →`, i.e.
`D.slab.DerivativeBoundBefore Ctime qcan D.endTime` unfolded, with the same `Ctime` as the history
clauses (S supplies it from its own derivative hypothesis). The binder order changed from
`theorem X (P₀) (g₀) (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0) (hmargin : Dtrace + 1 ≤ Dbig) (htol : 0 < tol)
(htolsmall : tol ≤ 1 / 1000) (hr : transitionEnd + tol⁻¹ + 1 < r) (hfit : 64 * (r + tol⁻¹) < Dtrace) :
∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧ ∃ εold δold : ℝ, …` to
`theorem X (P₀) (g₀) : ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace → ∃ εold δold : ℝ, …`
(same change in the four `PreparedHistoryCutoff` initial-identification theorems; the
prepared-history version takes `(Dtrace r tol a₀) (Ctime)` with `0 < a₀`). So `fixed` and
`recenterConstant` are fixed before `Λ` and every constant of C; the old shape follows by
instantiation. `Dbig := max Dcap (Dtrace + 1)` is S's choice (`le_max_right`).

## Update 2026-09-26 (coarse+fine factory F*; lane SFR, accepted by ACC6)

F* = `exists_horn_cutoff_record_with_uniform_volume_debit_of_spatiallyCanonical_of_fineCutNecks`
(`Contract/PoincareHornCutoffRecordOfFineCutNecks.lean`; the fine records in `Contract/HornFineCutNecks`
and `Contract/HornFineCutoffRecord`) is the factory on spatial witnesses with a fine-neck premise at the
cut. The premise, on the presentation (`TerminalCorePresentation` namespace):
```
def FineCutNecks (εc Qc : ℝ) : Prop :=
  ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (x : D.slab.terminalRegularOpen),
    x ∈ interior (range fun p : HalfNeckCylinder => P.horn c e p.1) →
    Qc ≤ metricScalarAt D.terminal.metric x →
    ∃ (δ : ℝ) (k : ℕ) (N : NormalizedNeck D.terminal.metric δ k),
      N.center = x ∧ δ ≤ εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ k
```
Binder order of F* (`OPUS_FILL_LOG_SFR.md` (2)):
`(P₀) (g₀) : ∃ fixed recenterConstant, 4 ≤ recenterConstant ∧ ∃ εP εbar, 0 < εP ∧ 0 < εbar ∧ εbar < 1/11 ∧
∀ Dtrace Dbig r tol Ctime, (margins) → ∃ εold δold, … ∧ ∀ m accuracy (0 <) ηrecord (0 <), ∃ δ εcut,
0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < εcut ∧ εcut ≤ εP ∧ ∀ C1 C2, 1 ≤ C2 → ∃ C Λ, 1 ≤ C ∧ 1 ≤ Λ ∧
∀ qcan originalCoreFloor protectedFloor Kfine, (positivity, 0 ≤ Kfine) → ∃ Q v, 0 < Q ∧ 0 < v ∧
v = Q ^ (-3/2) ∧ ∀ p₀ (class of p₀ at Dbig, tol, εold) H initial, … → ∀ ρold,
H.hasCanonicalCutoffRecords p₀ δold ρold → ∀ s G L hsing stepParameters, … → (history and slab
derivative clauses above qcan) → (floors) → G.SpatiallyCanonicalBefore εbar C1 C2 qcan s →
(∀ ρ hρ (P : TerminalCorePresentation (D.withNeckRadius ρ hρ) εP Λ),
  Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Q → P.FineCutNecks εcut Q) →
∃ ρ hρ, … (the existing factory conclusion)`.
F* takes no `κ`, no noncollapsing and no long-slab hypothesis: they belong to the supplier of the
fine premise. Remaining gaps F* → S (`OPUS_FILL_LOG_SFR.md` (5)): G1 = B12 (fine-neck supply on long
slabs, constant `Kfine` passed to F*) running; G2 = B13 (short slabs through the history window)
open; G3 (ε-monotonicity of spatial witnesses) closed by
`IncomingSlab.spatiallyCanonicalBefore_mono_eps` (`Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessMonotone.lean`);
G4 = B14 (record bounds `δbound := min δmax δold`, `ηrecord`, `p₀`, repackaging into S's
`∃ Q E hinit q`) running.

## Update 2026-09-26 (S ⇐ `hlong`; lanes SB12/SB14, accepted by ACC7)

`uniformDebitSurgeryStepStrong_of_long_slabs P₀ g₀ hlong : UniformDebitSurgeryStepStrong P₀ g₀`
(`Contract/UniformDebitSurgeryStepOfFactory.lean`) is the final S reduction: F* fed by B12's fine
cut necks (`TerminalCorePresentation.exists_fineCutNecks_of_long_terminal_slab`,
`Contract/HornFineCutNecksLongSlab.lean`, `∃ eta εcone` first so that `ε := min εbar (min εF εcone)`
is chosen before the constants), with `Λ := recenterConstant`, record bounds `min δold δmax`,
`min ρmax 1`, and the terminal limit metric from `IncomingSlab.nonempty_terminalLimitMetric`. Its
only hypothesis is `hlong : ∀ B θ : ℝ, 0 < B → 0 < θ → ∃ Qθ : ℝ, ∀ H : RetainedCoreHistory P₀,
InitialIdentification P₀ g₀ H.toHistory → H.horizon < B → ∀ s (G : (H.stage last).IncomingSlab
(H.time last) s), s ≤ B → G.flow.base.metric (H.time last) = H.initialMetric last →
G.SingularEndpoint → ∀ Qc, Qθ ≤ Qc → 2 * θ ≤ Qc * (s - H.time last)`: every singular final slab is
long at the fine threshold. This is G2 = B13 (short slabs), which `OPUS_FILL_LOG_SB13.md` shows is
the Crossing X-core applied to horn points; the S leaf closes when that core is built.

## Update 2026-09-26 (B3e on arbitrary slices; lane B3F, accepted by ACC8)

The first input of B13 (`hlong`), bounded curvature at distance on arbitrary slices, is now proved on
both slabs: `RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal` and
`…_event` (`Topology/BoundedCurvatureAtDistanceSlice{Terminal,Event}.lean`), for points that are not
cap-window points. The rebased form (`hRP`), maximal traced depth, the ancient κ-limit's bounded
curvature through the history (B6d glue, restated headline B11) and the cap-window exclusion remain
open; `hlong` is still the only hypothesis of S.

## Update 2026-09-26 (ACC9)

B13 (`hlong`) is the Crossing X-core applied to horn points. ACC9 accepted the Crossing base-slice
bricks BS1–BS5/BS7 (bounded curvature at distance on the sliver `[t₀, t]`, event and terminal forms,
`Topology/BoundedCurvatureAtDistanceSliver.lean`) and the B6d glue B4–B6 (neck alternatives of the
ancient limit from the survivor maps). BS6, B7's κ-variant and B11 remain; `hlong` is still the only
hypothesis of S.

## Update 2026-09-26 (ACC10; review H12, DESIGN_B13)

Review H12 (`consult/H12-s-fineCutNeckSupply-review-digest.md`): `hlong` is NOT a supplied input. The
reduction `uniformDebitSurgeryStepStrong_of_long_slabs` is correct and `hlong` is not refuted, but no
supplier exists. S is now reduced to the interface `FineCutNeckSupply` (T5, accepted:
`Contract/UniformDebitSurgeryStepOfFineCutNeckSupply.lean`,
`uniformDebitSurgeryStepStrong_of_fineCutNeckSupply`). T1 (terminal cap-side obstruction,
`Topology/TerminalCapSideExclusion.lean`) is DONE; T2 is running; T4 (the supply) is blocked on the
supply fork (interface strengthening vs fixed-parameter X-core vs reordering F*), laid out by the
running design lane DESIGN_S_SUPPLY. Once T4 lands the skeleton leaf is the one-liner
`uniformDebitSurgeryStepStrong_of_fineCutNeckSupply P₀ g₀ (fineCutNeckSupply P₀ g₀)`.
